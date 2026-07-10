import LambdaLab.Biparser.Mixfix.Precedence
import LambdaLab.Biparser.Mixfix.RightSublist

/-!
# Generic deterministic mixfix parser (in progress)

A precedence-climbing parser over an arbitrary `Grammar` — the deterministic `Option`
generalization of the verified `Concrete.lean` blueprint. Because `headsDistinct` is a
grammar field, dispatch is deterministic (at most one operator matches a leading token);
a precedence-incomparable input simply returns `none` ("add parentheses").

This file currently holds the **grammar-agnostic foundation**, ported from the reference
`Parser/Mixfix/Parse.lean` (these pieces are model-independent — they don't care whether
the parser returns one result or all): the precedence/body termination measures, the
operator classification (`leftRec`/`isJuxt`/`isInfxl`), `Expr.reindex`, the fold smart
constructors, and the variable leaf `parseVar`. The recursive `parseAt` core — the mutual
block that dispatches on the leading token and climbs the precedence DAG — is next.
-/

namespace LambdaLab.Biparser.Mixfix

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

/-! ## Termination measures -/

/-- The secondary termination measure of a level: `base · 4 + phase`. -/
def Level.measure {sep : Char → Bool} {Ent : Type} {E : Entry sep Ent} : Level E → Nat
  | .loosest     => E.topRank * 4 + 1
  | .tighter a   => E.rank a * 4 + 1
  | .tighterEq a => E.rank a * 4 + 3

/-- The secondary measure of an operator body: one more than the leading hole's
level measure, or `0` when the body starts with a `namePart`. -/
def partsMeasure {G : Grammar} : List (Part G) → Nat
  | .hole _ l :: _ => Level.measure l + 1
  | _              => 0

theorem partsMeasure_inner_eq_zero (n : Notation G.isSep G.Ent) :
    partsMeasure (Notation.toParts (G := G) n) = 0 := by
  cases n <;> rfl

/-! ## Operator classification -/

/-- The **left-recursive** operators (body leads with a `.tighterEq` hole): juxt
and left-assoc infix. Parsed by a fold instead of `parseParts`. -/
def Operator.leftRec {sep : Char → Bool} {Ent : Type} : Operator sep Ent → Bool
  | .juxt    => true
  | .infxl _ => true
  | _        => false

def Operator.isJuxt {sep : Char → Bool} {Ent : Type} : Operator sep Ent → Bool
  | .juxt => true
  | _     => false

theorem Operator.eq_juxt {sep : Char → Bool} {Ent : Type} {o : Operator sep Ent}
    (h : o.isJuxt = true) : o = Operator.juxt := by cases o <;> simp_all [Operator.isJuxt]

theorem Operator.ne_juxt {sep : Char → Bool} {Ent : Type} {o : Operator sep Ent}
    (h : ¬ (o.isJuxt = true)) : o ≠ Operator.juxt := fun he => h (by rw [he]; rfl)

def Operator.isInfxl {sep : Char → Bool} {Ent : Type} : Operator sep Ent → Bool
  | .infxl _ => true
  | _        => false

theorem Operator.not_isJuxt_of_isInfxl {sep : Char → Bool} {Ent : Type} {o : Operator sep Ent}
    (h : o.isInfxl = true) : o.isJuxt = false := by
  cases o <;> simp_all [Operator.isInfxl, Operator.isJuxt]

theorem Operator.leftRec_eq_false {sep : Char → Bool} {Ent : Type} {o : Operator sep Ent}
    (hj : ¬ o.isJuxt = true) (hl : ¬ o.isInfxl = true) : o.leftRec = false := by
  cases o <;> simp_all [Operator.isJuxt, Operator.isInfxl, Operator.leftRec]

/-- An operator body measures strictly below its own `tighterEq` level. -/
theorem partsMeasure_parts_lt (e : G.Ent) (a : (G.entry e).Op)
    (hne : ((G.entry e).operator a).leftRec = false) :
    partsMeasure (Operator.body e a) < Level.measure (Level.tighterEq a) := by
  unfold Operator.body
  cases h : (G.entry e).operator a with
  | closed n =>
      rw [partsMeasure_inner_eq_zero]; simp only [Level.measure]; omega
  | prefx n =>
      have hz : partsMeasure (Notation.toParts (G := G) n ++ [.hole e (.tighter a)]) = 0 := by
        cases n <;> rfl
      rw [hz]; simp only [Level.measure]; omega
  | infx n => simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]; omega
  | infxl n => rw [h, Operator.leftRec] at hne; exact absurd hne (by simp)
  | infxr n => simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]; omega
  | juxt => rw [h, Operator.leftRec] at hne; exact absurd hne (by simp)
  | postfx n => simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]; omega

/-! ## Tree utilities -/

/-- Weaken the level of an expression within its entry: only the level witness
changes, so the flattening is untouched. -/
def Expr.reindex {e : G.Ent} {l l' : Level (G.entry e)}
    (h : ∀ o, Level.condition l o → Level.condition l' o) : Expr G e l → Expr G e l'
  | .op o hc parts => .op o (h o hc) parts
  | .var t hv => .var t hv

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

/-! ## Leaf: variables

The one non-recursive leaf. Deterministic: a leading `isVar` token is a variable leaf
(valid at every level); otherwise no variable parse. `varDisjoint` guarantees this token
is not also an operator part, so this never conflicts with operator dispatch. -/

def parseVar (e : G.Ent) (l : Level (G.entry e)) :
    (tkns : List (Token G.isSep)) → Option (Expr G e l × RightSublist tkns)
  | [] => none
  | t :: rest =>
      if h : (G.entry e).isVar t = true then
        some (Expr.var t h, RightSublist.consTail t rest)
      else none

/-! ## The recursive core

Deterministic precedence climbing. `parseExpr e l` parses one expression of entry `e`
constrained to level `l`; `parseExprList` walks the candidate operators of a level,
taking the **first** that succeeds (`headsDistinct` ⇒ at most one does); `parseParts`
parses an operator body left-to-right.

Left-recursive operators (`juxt`, `infxl`) are not yet parsed — at their `.tighterEq`
level the parser falls through to `.tighter` instead of running a fold. Everything else
(closed, prefix, non-assoc infix, right-assoc infix, postfix) parses fully.

Termination is the reference's lexicographic measure `(tkns.length, Level.measure l /
Level.base l * 4 / partsMeasure ps, phase)`; `RightSublist.length_lt` supplies the
`tkns.length` drop when a sub-parse's leftover is fed onward. -/

-- `h : … .leftRec = true` reads as unused (it is consumed only in `decreasing_by`).
set_option linter.unusedVariables false in
mutual
  /-- Parse one expression of entry `e` constrained to level `l`. -/
  def parseExpr (e : G.Ent) (l : Level (G.entry e)) (tkns : List (Token G.isSep)) :
      Option (Expr G e l × RightSublist tkns) :=
    match l with
    | .loosest =>
        (parseExprList e .loosest (G.entry e).loosest (fun c hc _o hco => ⟨c, hc, hco⟩)
          (fun _ hc => (G.entry e).rank_lt_topRank hc) tkns).orElse
          (fun _ => parseVar e .loosest tkns)
    | .tighter a =>
        (parseExprList e (.tighter a) ((G.entry e).tighter a)
          (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco)
          (fun _ hc => (G.entry e).rank_lt hc) tkns).orElse
          (fun _ => parseVar e (.tighter a) tkns)
    | .tighterEq a =>
        if hj : ((G.entry e).operator a).isJuxt = true then
          parseJuxt e a (Operator.eq_juxt hj) tkns
        else if hl : ((G.entry e).operator a).isInfxl = true then
          parseInfixL e a hl tkns
        else
          let fallthrough : Option (Expr G e (.tighterEq a) × RightSublist tkns) :=
            (parseExpr e (.tighter a) tkns).map
              (fun x => (x.1.reindex (l := .tighter a) (l' := .tighterEq a)
                          (fun _o hh => Tighter.toTighterEq
                            (show Tighter (G.entry e).tighter a _o from hh)), x.2))
          ((parseParts (Operator.body e a) tkns).map
            (fun x => ((Expr.op a TighterEq.refl x.1 : Expr G e (.tighterEq a)), x.2))).orElse
            (fun _ => fallthrough)
  termination_by (tkns.length, Level.measure l, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (partsMeasure_parts_lt _ _ (Operator.leftRec_eq_false hj hl)))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure, Level.base]; omega))

  /-- Walk the candidate operators `cs` of a level, taking the first that succeeds. -/
  def parseExprList (e : G.Ent) (l : Level (G.entry e)) (cs : List (G.entry e).Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq (G.entry e).tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, (G.entry e).rank c < Level.base l)
      (tkns : List (Token G.isSep)) : Option (Expr G e l × RightSublist tkns) :=
    match cs, h, hrank with
    | [], _, _ => none
    | c :: rest, h, hrank =>
        ((parseExpr e (.tighterEq c) tkns).map
          (fun x => (x.1.reindex (l := .tighterEq c) (l' := l)
                      (fun o hh => h c List.mem_cons_self o
                        (show TighterEq (G.entry e).tighter c o from hh)), x.2))).orElse
          (fun _ => parseExprList e l rest (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
                      (fun c' hc' => hrank c' (List.mem_cons_of_mem _ hc')) tkns)
  termination_by (tkns.length, Level.base l * 4, cs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (by have := hrank c List.mem_cons_self
              first | (simp only [Level.measure]; omega) | omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _
          (by first | (simp only [List.length_cons]; omega) | omega))

  /-- Parse an operator body `ps` left-to-right: match each `namePart`, recurse into
  `parseExpr` at each `hole`'s (entry, level). -/
  def parseParts : (ps : List (Part G)) → (tkns : List (Token G.isSep)) →
      Option (Parts G ps × RightSublist tkns)
    | [], _ => none
    | [.namePart tk], tkns =>
        match tkns with
        | t :: rest => if t = tk then some (Parts.namePart tk Parts.nil, RightSublist.consTail t rest) else none
        | []        => none
    | [.hole e l], tkns =>
        (parseExpr e l tkns).map (fun x => (Parts.hole x.1 Parts.nil, x.2))
    | .namePart tk :: y :: rest', tkns =>
        match tkns with
        | t :: ts =>
            if t = tk then
              (parseParts (y :: rest') ts).map
                  (fun z => (Parts.namePart tk z.1, (RightSublist.consTail t ts).trans z.2))
            else none
        | [] => none
    | .hole e l :: y :: rest', tkns =>
        (parseExpr e l tkns).bind (fun x =>
          (parseParts (y :: rest') x.2.list).map
              (fun z => (Parts.hole x.1 z.1, x.2.trans z.2)))
  termination_by ps tkns => (tkns.length, partsMeasure ps, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by first | (simp only [partsMeasure]; omega) | omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)
      | exact Prod.Lex.left _ _ (by first | (simp only [List.length_cons]; omega) | omega)

  /-- Parse an application chain `f x y …` left-associatively: the first operand, then
  as many further argument atoms as possible (greedy). -/
  def parseJuxt (e : G.Ent) (j : (G.entry e).Op) (hj : (G.entry e).operator j = Operator.juxt)
      (tkns : List (Token G.isSep)) : Option (Expr G e (Level.tighterEq j) × RightSublist tkns) :=
    match parseExpr e (Level.tighter j) tkns with
    | none => none
    | some (x, s1) =>
        let lone : Expr G e (Level.tighterEq j) :=
          x.reindex (l := Level.tighter j) (l' := Level.tighterEq j)
            (fun _o hh => Tighter.toTighterEq (show Tighter (G.entry e).tighter j _o from hh))
        match parseJuxtExtend e j hj lone s1.list with
        | none => some (lone, s1)
        | some (final, s2) => some (final, s1.trans s2)
  termination_by (tkns.length, (G.entry e).rank j * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := s1.length_lt; omega)

  /-- Fold one more argument atom onto an application accumulator, greedily. -/
  def parseJuxtExtend (e : G.Ent) (j : (G.entry e).Op) (hj : (G.entry e).operator j = Operator.juxt)
      (acc : Expr G e (Level.tighterEq j)) (tkns : List (Token G.isSep)) :
      Option (Expr G e (Level.tighterEq j) × RightSublist tkns) :=
    match parseExpr e (Level.tighter j) tkns with
    | none => none
    | some (x, s) =>
        let acc' := Expr.juxtApp hj acc x
        match parseJuxtExtend e j hj acc' s.list with
        | none => some (acc', s)
        | some (final, s2) => some (final, s.trans s2)
  termination_by (tkns.length, (G.entry e).rank j * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := s.length_lt; omega)

  /-- Parse a left-associative chain `a ∘ b ∘ c …`: the first operand, then as many
  `∘ rhs` segments as possible (greedy). -/
  def parseInfixL (e : G.Ent) (o : (G.entry e).Op) (hl : ((G.entry e).operator o).isInfxl = true)
      (tkns : List (Token G.isSep)) : Option (Expr G e (Level.tighterEq o) × RightSublist tkns) :=
    match parseExpr e (Level.tighter o) tkns with
    | none => none
    | some (x, s1) =>
        let lone : Expr G e (Level.tighterEq o) :=
          x.reindex (l := Level.tighter o) (l' := Level.tighterEq o)
            (fun _o hh => Tighter.toTighterEq (show Tighter (G.entry e).tighter o _o from hh))
        match parseInfixLExtend e o hl lone s1.list with
        | none => some (lone, s1)
        | some (final, s2) => some (final, s1.trans s2)
  termination_by (tkns.length, (G.entry e).rank o * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := s1.length_lt; omega)

  /-- Fold one more `∘ rhs` segment onto a left-assoc accumulator, greedily. -/
  def parseInfixLExtend (e : G.Ent) (o : (G.entry e).Op) (hl : ((G.entry e).operator o).isInfxl = true)
      (acc : Expr G e (Level.tighterEq o)) (tkns : List (Token G.isSep)) :
      Option (Expr G e (Level.tighterEq o) × RightSublist tkns) :=
    match parseParts (Operator.body e o).tail tkns with
    | none => none
    | some (tp, s) =>
        let acc' := Expr.infxlApp hl acc tp
        match parseInfixLExtend e o hl acc' s.list with
        | none => some (acc', s)
        | some (final, s2) => some (final, s.trans s2)
  termination_by (tkns.length, (G.entry e).rank o * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by rw [partsMeasure_infxl_tail hl]; omega))
      | exact Prod.Lex.left _ _ (by have := s.length_lt; omega)
end

end LambdaLab.Biparser.Mixfix
