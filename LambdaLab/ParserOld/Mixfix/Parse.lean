import LambdaLab.ParserOld.Mixfix.Tree

/-!
# Parser for the multi-entry `Part`/`Parts` model (all parses)

A precedence-climbing parser over the family of entries. An operator of entry `e`
has body `Operator.body e o : List (Part G)`, each `Part` a literal `namePart` or
a `hole (e' : G.Ent) (Level (G.entry e'))` — recursive (host entry) or cross-entry
are the *same* construct. The parser returns **all** parses; termination is by
well-founded recursion on `(tkns.length, Level.measure l, list-length)`. Interior
cross-entry holes always follow a consumed name token (so `tkns.length` drops);
the only same-token descent is intra-entry, going `.tighter`, ordered by a per-entry
rank manufactured from `tighter_wf`.

No correctness proofs — only termination.
-/

namespace LambdaLab.ParserOld.Mixfix

open LambdaLab.ParserOld

variable {G : Grammar}

/-! ## Precedence-order plumbing -/

theorem TighterEq.toTighterOrEq {Op : Type} {t : Op → List Op} {a b : Op}
    (h : TighterEq t a b) : a = b ∨ Tighter t a b := by
  induction h with
  | refl => exact Or.inl rfl
  | step hmem _ ih =>
      cases ih with
      | inl hEq => exact Or.inr (hEq ▸ Tighter.base hmem)
      | inr hT  => exact Or.inr (Tighter.step hmem hT)

theorem Tighter.ofMemTighterEq {Op : Type} {t : Op → List Op} {a b o : Op}
    (hmem : b ∈ t a) (h : TighterEq t b o) : Tighter t a o := by
  cases h.toTighterOrEq with
  | inl hEq => exact hEq ▸ Tighter.base hmem
  | inr hT  => exact Tighter.step hmem hT

/-- Weaken the level of an expression within its entry: only the level witness
changes, so the flattening is untouched. -/
def Expr.reindex {e : G.Ent} {l l' : Level (G.entry e)}
    (h : ∀ o, Level.condition l o → Level.condition l' o) : Expr G e l → Expr G e l'
  | .op o hc parts => .op o (h o hc) parts
  | .var t hv => .var t hv

/-! ## A per-entry `Nat` rank for the termination measure -/

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A `Nat` rank derived from an entry's well-founded `tighter` graph. -/
def Entry.rank {Ent : Type} (E : Entry Ent) (a : E.Op) : Nat :=
  E.tighter_wf.fix (C := fun _ => Nat)
    (fun a ih => ((E.tighter a).attach.map (fun b => ih b.1 b.2 + 1)).foldr Nat.max 0) a

theorem Entry.rank_eq {Ent : Type} (E : Entry Ent) (a : E.Op) :
    E.rank a = ((E.tighter a).attach.map (fun b => E.rank b.1 + 1)).foldr Nat.max 0 :=
  WellFounded.fix_eq _ _ _

theorem Entry.rank_lt {Ent : Type} (E : Entry Ent) {a b : E.Op} (h : b ∈ E.tighter a) :
    E.rank b < E.rank a := by
  rw [E.rank_eq a]
  have hmem : E.rank b + 1 ∈ (E.tighter a).attach.map (fun c => E.rank c.1 + 1) :=
    List.mem_map.mpr ⟨⟨b, h⟩, List.mem_attach _ _, rfl⟩
  have := le_foldr_max hmem
  omega

def Entry.topRank {Ent : Type} (E : Entry Ent) : Nat := (E.loosest.map E.rank).foldr Nat.max 0 + 1

theorem Entry.rank_lt_topRank {Ent : Type} (E : Entry Ent) {r : E.Op} (h : r ∈ E.loosest) :
    E.rank r < E.topRank := by
  have hmem : E.rank r ∈ E.loosest.map E.rank := List.mem_map.mpr ⟨r, h, rfl⟩
  have := le_foldr_max hmem
  unfold Entry.topRank
  omega

/-- The looseness base of a level (the candidate-worklist's measure). -/
def Level.base {Ent : Type} {E : Entry Ent} : Level E → Nat
  | .loosest     => E.topRank
  | .tighter a   => E.rank a
  | .tighterEq a => E.rank a

/-- The secondary termination measure of a level: `base · 4 + phase`. -/
def Level.measure {Ent : Type} {E : Entry Ent} : Level E → Nat
  | .loosest     => E.topRank * 4 + 1
  | .tighter a   => E.rank a * 4 + 1
  | .tighterEq a => E.rank a * 4 + 3

/-- The secondary measure of an operator body: one more than the leading hole's
level measure, or `0` when the body starts with a `namePart`. -/
def partsMeasure {G : Grammar} : List (Part G) → Nat
  | .hole _ l :: _ => Level.measure l + 1
  | _              => 0

theorem partsMeasure_inner_eq_zero (n : Notation G.Ent) :
    partsMeasure (Notation.toParts (G := G) n) = 0 := by
  cases n <;> rfl

/-- The **left-recursive** operators (body leads with a `.tighterEq` hole): juxt
and left-assoc infix. Parsed by a fold instead of `parseParts`. -/
def Operator.leftRec {Ent : Type} : Operator Ent → Bool
  | .juxt    => true
  | .infxl _ => true
  | _        => false

/-- An operator body measures strictly below its own `tighterEq` level. -/
theorem partsMeasure_parts_lt (e : G.Ent) (a : (G.entry e).Op)
    (hne : ((G.entry e).operator a).leftRec = false) :
    partsMeasure (Operator.body e a) < Level.measure (Level.tighterEq a) := by
  unfold Operator.body
  cases h : (G.entry e).operator a with
  | closed n =>
      rw [partsMeasure_inner_eq_zero]
      simp only [Level.measure]; omega
  | prefx n =>
      have hz : partsMeasure (Notation.toParts (G := G) n ++ [.hole e (.tighter a)]) = 0 := by
        cases n <;> rfl
      rw [hz]
      simp only [Level.measure]; omega
  | infx n =>
      simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]
      omega
  | infxl n => rw [h, Operator.leftRec] at hne; exact absurd hne (by simp)
  | infxr n =>
      simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]
      omega
  | juxt => rw [h, Operator.leftRec] at hne; exact absurd hne (by simp)
  | postfx n =>
      simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]
      omega

/-- Parse a single variable leaf at entry `e`, level `l`. -/
def parseVar (e : G.Ent) (l : Level (G.entry e)) :
    (tkns : List Token) → List (Expr G e l × RightSublist tkns)
  | [] => []
  | t :: rest =>
      if h : (G.entry e).isVar t = true then [(Expr.var t h, RightSublist.cons t rest)] else []

/-- The body of a juxtaposition operator. -/
theorem Operator.body_juxt {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) :
    Operator.body e j = [Part.hole e (Level.tighterEq j), Part.hole e (Level.tighter j)] := by
  unfold Operator.body; rw [hj]

/-- Smart constructor for one application node `f x`. -/
def Expr.juxtApp {e : G.Ent} {j : (G.entry e).Op} (hj : (G.entry e).operator j = Operator.juxt)
    (f : Expr G e (Level.tighterEq j)) (x : Expr G e (Level.tighter j)) :
    Expr G e (Level.tighterEq j) :=
  Expr.op j TighterEq.refl ((Operator.body_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil))

def Operator.isJuxt {Ent : Type} : Operator Ent → Bool
  | .juxt => true
  | _     => false

theorem Operator.eq_juxt {Ent : Type} {o : Operator Ent} (h : o.isJuxt = true) :
    o = Operator.juxt := by cases o <;> simp_all [Operator.isJuxt]

theorem Operator.ne_juxt {Ent : Type} {o : Operator Ent} (h : ¬ (o.isJuxt = true)) :
    o ≠ Operator.juxt := fun he => h (by rw [he]; rfl)

def Operator.isInfxl {Ent : Type} : Operator Ent → Bool
  | .infxl _ => true
  | _        => false

theorem Operator.not_isJuxt_of_isInfxl {Ent : Type} {o : Operator Ent} (h : o.isInfxl = true) :
    o.isJuxt = false := by cases o <;> simp_all [Operator.isInfxl, Operator.isJuxt]

theorem Operator.leftRec_eq_false {Ent : Type} {o : Operator Ent}
    (hj : ¬ o.isJuxt = true) (hl : ¬ o.isInfxl = true) : o.leftRec = false := by
  cases o <;> simp_all [Operator.isJuxt, Operator.isInfxl, Operator.leftRec]

/-- A left-assoc body splits as its chaining left operand hole and the tail. -/
theorem Operator.body_infxl_cons {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) :
    Operator.body e o = Part.hole e (Level.tighterEq o) :: (Operator.body e o).tail := by
  cases hop : (G.entry e).operator o with
  | infxl n => unfold Operator.body; rw [hop]; rfl
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- The tail of a left-assoc body leads with a name token (`partsMeasure = 0`). -/
theorem partsMeasure_infxl_tail {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) :
    partsMeasure (Operator.body e o).tail = 0 := by
  cases hop : (G.entry e).operator o with
  | infxl n => unfold Operator.body; rw [hop]; cases n <;> rfl
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- Smart constructor for one left-assoc fold step `(acc) ∘ rhs`. -/
def Expr.infxlApp {e : G.Ent} {o : (G.entry e).Op} (hl : ((G.entry e).operator o).isInfxl = true)
    (acc : Expr G e (Level.tighterEq o)) (tail : Parts G (Operator.body e o).tail) :
    Expr G e (Level.tighterEq o) :=
  Expr.op o TighterEq.refl ((Operator.body_infxl_cons hl).symm ▸ Parts.hole acc tail)

/-! ## The parser -/

set_option linter.unusedSimpArgs false in
mutual
  /-- All parses of an expression of entry `e` constrained to level `l`. -/
  def parseExpr : (e : G.Ent) → (l : Level (G.entry e)) → (tkns : List Token) →
      List (Expr G e l × RightSublist tkns)
    | e, .loosest, tkns =>
        parseExprList e .loosest (G.entry e).loosest (fun c hc _o hco => ⟨c, hc, hco⟩)
          (fun _ hc => (G.entry e).rank_lt_topRank hc) tkns
        ++ parseVar e .loosest tkns
    | e, .tighter a, tkns =>
        parseExprList e (.tighter a) ((G.entry e).tighter a)
          (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco)
          (fun _ hc => (G.entry e).rank_lt hc) tkns
        ++ parseVar e (.tighter a) tkns
    | e, .tighterEq a, tkns =>
        if hj : ((G.entry e).operator a).isJuxt = true then
          parseJuxt e a (Operator.eq_juxt hj) tkns
        else if hl : ((G.entry e).operator a).isInfxl = true then
          parseInfixL e a hl tkns
        else
          (parseParts (Operator.body e a) tkns).map
              (fun x => ((Expr.op a TighterEq.refl x.1 : Expr G e (.tighterEq a)), x.2))
          ++ (parseExpr e (.tighter a) tkns).map
              (fun x => (x.1.reindex (l := .tighter a) (l' := .tighterEq a)
                          (fun _ hh => Tighter.toTighterEq (show Tighter (G.entry e).tighter a _ from hh)), x.2))
  termination_by e l tkns => (tkns.length, Level.measure l, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (partsMeasure_parts_lt _ _ (Operator.leftRec_eq_false (by assumption) (by assumption))))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure, Level.base]; omega))

  /-- Concatenate the parses contributed by each candidate operator `c ∈ cs` of
  entry `e`: parse at `c`'s own level and reindex up to `l`. -/
  def parseExprList (e : G.Ent) (l : Level (G.entry e)) (cs : List (G.entry e).Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq (G.entry e).tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, (G.entry e).rank c < Level.base l) :
      (tkns : List Token) → List (Expr G e l × RightSublist tkns) :=
    fun tkns =>
      match cs, h, hrank with
      | [], _, _ => []
      | c :: rest, h, hrank =>
          (parseExpr e (.tighterEq c) tkns).map
              (fun x => (x.1.reindex (l := .tighterEq c) (l' := l)
                          (fun o hh => h c List.mem_cons_self o
                            (show TighterEq (G.entry e).tighter c o from hh)), x.2))
          ++ parseExprList e l rest (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
              (fun c' hc' => hrank c' (List.mem_cons_of_mem _ hc')) tkns
  termination_by tkns => (tkns.length, Level.base l * 4, cs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (by have := hrank c List.mem_cons_self
              first | (simp only [Level.measure]; omega) | omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _
          (by first | (simp only [List.length_cons]; omega) | omega))

  /-- Parse an operator body `ps` left-to-right: match each `namePart`, recurse
  into `parseExpr` at each `hole`'s (entry, level). -/
  def parseParts : (ps : List (Part G)) → (tkns : List Token) →
      List (Parts G ps × RightSublist tkns)
    | [], _ => []
    | [.namePart tk], tkns =>
        match tkns with
        | t :: rest => if t = tk then [(Parts.namePart tk Parts.nil, RightSublist.cons t rest)] else []
        | []        => []
    | [.hole e l], tkns =>
        (parseExpr e l tkns).map (fun x => (Parts.hole x.1 Parts.nil, x.2))
    | .namePart tk :: y :: rest', tkns =>
        match tkns with
        | t :: ts =>
            if t = tk then
              (parseParts (y :: rest') ts).map
                  (fun z => (Parts.namePart tk z.1, (RightSublist.cons t ts).trans z.2))
            else []
        | [] => []
    | .hole e l :: y :: rest', tkns =>
        (parseExpr e l tkns).flatMap (fun x =>
          (parseParts (y :: rest') x.2.list).map
              (fun z => (Parts.hole x.1 z.1, x.2.trans z.2)))
  termination_by ps tkns => (tkns.length, partsMeasure ps, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by first | (simp only [partsMeasure]; omega) | omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)
      | exact Prod.Lex.left _ _ (by first | (simp only [List.length_cons]; omega) | omega)

  /-- Parse an application chain `f x y …` left-associatively by iteration. -/
  def parseJuxt (e : G.Ent) (j : (G.entry e).Op) (hj : (G.entry e).operator j = Operator.juxt) :
      (tkns : List Token) → List (Expr G e (Level.tighterEq j) × RightSublist tkns) :=
    fun tkns =>
      (parseExpr e (Level.tighter j) tkns).flatMap (fun x =>
        let lone : Expr G e (Level.tighterEq j) :=
          x.1.reindex (l := Level.tighter j) (l' := Level.tighterEq j)
            (fun _o hh => Tighter.toTighterEq (show Tighter (G.entry e).tighter j _o from hh))
        (lone, x.2) :: (parseJuxtExtend e j hj lone x.2.list).map (fun y => (y.1, x.2.trans y.2)))
  termination_by tkns => (tkns.length, (G.entry e).rank j * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- Fold one more argument atom onto an application accumulator. -/
  def parseJuxtExtend (e : G.Ent) (j : (G.entry e).Op) (hj : (G.entry e).operator j = Operator.juxt)
      (acc : Expr G e (Level.tighterEq j)) :
      (tkns : List Token) → List (Expr G e (Level.tighterEq j) × RightSublist tkns) :=
    fun tkns =>
      (parseExpr e (Level.tighter j) tkns).flatMap (fun x =>
        let acc' : Expr G e (Level.tighterEq j) := Expr.juxtApp hj acc x.1
        (acc', x.2) :: (parseJuxtExtend e j hj acc' x.2.list).map (fun y => (y.1, x.2.trans y.2)))
  termination_by tkns => (tkns.length, (G.entry e).rank j * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- Parse a left-associative chain `a ∘ b ∘ c …` by iteration. -/
  def parseInfixL (e : G.Ent) (o : (G.entry e).Op) (hl : ((G.entry e).operator o).isInfxl = true) :
      (tkns : List Token) → List (Expr G e (Level.tighterEq o) × RightSublist tkns) :=
    fun tkns =>
      (parseExpr e (Level.tighter o) tkns).flatMap (fun x =>
        let lone : Expr G e (Level.tighterEq o) :=
          x.1.reindex (l := Level.tighter o) (l' := Level.tighterEq o)
            (fun _o hh => Tighter.toTighterEq (show Tighter (G.entry e).tighter o _o from hh))
        (lone, x.2) :: (parseInfixLExtend e o hl lone x.2.list).map (fun y => (y.1, x.2.trans y.2)))
  termination_by tkns => (tkns.length, (G.entry e).rank o * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- Fold one more `∘ rhs` segment onto a left-assoc accumulator. -/
  def parseInfixLExtend (e : G.Ent) (o : (G.entry e).Op) (hl : ((G.entry e).operator o).isInfxl = true)
      (acc : Expr G e (Level.tighterEq o)) :
      (tkns : List Token) → List (Expr G e (Level.tighterEq o) × RightSublist tkns) :=
    fun tkns =>
      (parseParts (Operator.body e o).tail tkns).flatMap (fun tp =>
        let acc' : Expr G e (Level.tighterEq o) := Expr.infxlApp hl acc tp.1
        (acc', tp.2) :: (parseInfixLExtend e o hl acc' tp.2.list).map (fun y => (y.1, tp.2.trans y.2)))
  termination_by tkns => (tkns.length, (G.entry e).rank o * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by rw [partsMeasure_infxl_tail hl]; omega))
      | exact Prod.Lex.left _ _ (by have := tp.2.length_lt; omega)
end

/-- All full parses of `tkns` at start entry `e` (consuming the entire input). -/
def parse (e : G.Ent) (tkns : List Token) : List (Expr G e .loosest) :=
  (parseExpr (G := G) e .loosest tkns).filterMap (fun x => if x.2.list = [] then some x.1 else none)

end LambdaLab.ParserOld.Mixfix
