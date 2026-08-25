import LambdaLab.Parser.IsoParser.Mixfix.Tree

/-!
# The general mixfix parser — a mutual well-founded recursion

A deterministic precedence-climbing parser over an arbitrary `Grammar Tok`: a plain **mutual
well-founded `def`** terminating on the lexicographic measure
`(input.length, Level.measure l, phase)` — descending a precedence level keeps the input and drops
the level component; consuming a token drops the length. No `fix` combinator; the round-trip laws
(next file) are proved by induction on this same measure.

Ported in shape from the `CBiparser` parser, but self-contained: abstract token alphabet `Tok`, and
the precedence `rank`/`topRank` are grammar *fields* (so the measure is immediate).
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

variable {Tok : Type}

/-! ## Progress witness: proper right sublists -/

/-- A leftover of `l` strictly shorter than it — the parser's proof of progress. -/
structure RightSublist (l : List Tok) where
  list : List Tok
  lt   : list.length < l.length

namespace RightSublist

/-- Dropping the head yields a strictly shorter leftover. -/
def consTail (a : Tok) (l : List Tok) : RightSublist (a :: l) := ⟨l, by simp⟩

/-- A shorter-leftover of a shorter-leftover is a shorter-leftover. -/
def trans {l : List Tok} (s : RightSublist l) (r : RightSublist s.list) : RightSublist l :=
  ⟨r.list, Nat.lt_trans r.lt s.lt⟩

@[simp] theorem consTail_list (a : Tok) (l : List Tok) : (consTail a l).list = l := rfl
@[simp] theorem trans_list {l : List Tok} (s : RightSublist l) (r : RightSublist s.list) :
    (s.trans r).list = r.list := rfl
theorem length_lt {l : List Tok} (r : RightSublist l) : r.list.length < l.length := r.lt

end RightSublist

/-! ## Precedence measures -/

variable {Ent : Type}

/-- Reaching a strictly-tighter operator (transitively) strictly decreases the rank. -/
theorem Entry.rank_lt_of_tighter (E : Entry Tok Ent) {a b : E.Op}
    (h : Tighter E.tighter a b) : E.rank b < E.rank a := by
  induction h with
  | single hmem    => exact E.rank_tighter _ _ hmem
  | tail _ hmem ih => exact Nat.lt_trans (E.rank_tighter _ _ hmem) ih

/-- The `Nat` looseness of a level: `loosest` sits at `topRank`, an operand level at its rank. -/
def Level.base {E : Entry Tok Ent} : Level E → Nat
  | .loosest     => E.topRank
  | .tighter a   => E.rank a
  | .tighterEq a => E.rank a

/-- The secondary termination measure of a level: `base · 4 + phase`. -/
def Level.measure {E : Entry Tok Ent} : Level E → Nat
  | .loosest     => E.topRank * 4 + 1
  | .tighter a   => E.rank a * 4 + 1
  | .tighterEq a => E.rank a * 4 + 3

/-- The secondary measure of an operator body: one more than the leading hole's level measure, or `0`
when the body starts with a `namePart`. -/
def partsMeasure {G : Grammar Tok} : List (Part G) → Nat
  | .hole _ l :: _ => Level.measure l + 1
  | _              => 0

theorem partsMeasure_inner_eq_zero {G : Grammar Tok} (n : Notation Tok G.Ent) :
    partsMeasure (Notation.toParts (G := G) n) = 0 := by
  cases n <;> rfl

/-! ## Operator classification -/

/-- The **left-recursive** operators (body leads with a `.tighterEq` hole): juxt and left-assoc
infix. Parsed by a fold instead of `parseParts`. -/
def Operator.leftRec {Tok Ent : Type} : Operator Tok Ent → Bool
  | .juxt    => true
  | .infxl _ => true
  | _        => false

def Operator.isJuxt {Tok Ent : Type} : Operator Tok Ent → Bool
  | .juxt => true
  | _     => false

theorem Operator.eq_juxt {Tok Ent : Type} {o : Operator Tok Ent}
    (h : o.isJuxt = true) : o = Operator.juxt := by cases o <;> simp_all [Operator.isJuxt]

def Operator.isInfxl {Tok Ent : Type} : Operator Tok Ent → Bool
  | .infxl _ => true
  | _        => false

theorem Operator.leftRec_eq_false {Tok Ent : Type} {o : Operator Tok Ent}
    (hj : ¬ o.isJuxt = true) (hl : ¬ o.isInfxl = true) : o.leftRec = false := by
  cases o <;> simp_all [Operator.isJuxt, Operator.isInfxl, Operator.leftRec]

/-- An operator body measures strictly below its own `tighterEq` level. -/
theorem partsMeasure_parts_lt {G : Grammar Tok} (e : G.Ent) (a : (G.entry e).Op)
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

/-- Weaken the level of an expression within its entry: only the level witness changes, so the
flattening is untouched. -/
def Expr.reindex {G : Grammar Tok} {e : G.Ent} {l l' : Level (G.entry e)}
    (h : ∀ o, Level.condition l o → Level.condition l' o) : Expr G e l → Expr G e l'
  | .op o hc parts => .op o (h o hc) parts
  | .var t hv => .var t hv

theorem Operator.body_juxt {G : Grammar Tok} {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) :
    Operator.body e j = [Part.hole e (Level.tighterEq j), Part.hole e (Level.tighter j)] := by
  unfold Operator.body; rw [hj]

/-- Smart constructor for one application node `f x`. -/
def Expr.juxtApp {G : Grammar Tok} {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (f : Expr G e (Level.tighterEq j)) (x : Expr G e (Level.tighter j)) :
    Expr G e (Level.tighterEq j) :=
  Expr.op j TighterEq.refl ((Operator.body_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil))

theorem Operator.body_infxl_cons {G : Grammar Tok} {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) :
    Operator.body e o = Part.hole e (Level.tighterEq o) :: (Operator.body e o).tail := by
  cases hop : (G.entry e).operator o with
  | infxl n => unfold Operator.body; rw [hop]; rfl
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- The tail of a left-assoc body leads with a name token (`partsMeasure = 0`). -/
theorem partsMeasure_infxl_tail {G : Grammar Tok} {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) :
    partsMeasure (Operator.body e o).tail = 0 := by
  cases hop : (G.entry e).operator o with
  | infxl n => unfold Operator.body; rw [hop]; cases n <;> rfl
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- Smart constructor for one left-assoc fold step `(acc) ∘ rhs`. -/
def Expr.infxlApp {G : Grammar Tok} {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    (acc : Expr G e (Level.tighterEq o)) (tail : Parts G (Operator.body e o).tail) :
    Expr G e (Level.tighterEq o) :=
  Expr.op o TighterEq.refl ((Operator.body_infxl_cons hl).symm ▸ Parts.hole acc tail)

/-! ## Leaf: variables -/

def parseVar {G : Grammar Tok} (e : G.Ent) (l : Level (G.entry e)) :
    (tkns : List Tok) → Option (Expr G e l × RightSublist tkns)
  | [] => none
  | t :: rest =>
      if h : (G.entry e).isVar t = true then
        some (Expr.var t h, RightSublist.consTail t rest)
      else none

/-! ## Longest match at the parser's two choice points

`parseExprList` picks among a level's candidate operators, and `parseExpr` at a `.tighterEq` level
picks between the operator's own body and a strictly tighter tree. **Both** take the longest match
rather than the first success, and both have to: a candidate that does not use its operator falls
through to a bare operand and so "succeeds" trivially, which under `orElse` would let candidate
order decide the parse. It is also what makes exactness provable — `Exact.lean`'s induction shows
at each choice point that the printed tree is *among* the alternatives, and longest match does the
rest. -/

/-- Prefer whichever parse consumed **more** (shorter leftover); ties go to the first argument. -/
def longer {α : Type} {tkns : List Tok}
    (a b : Option (α × RightSublist tkns)) : Option (α × RightSublist tkns) :=
  match a, b with
  | none,   b'     => b'
  | a',     none   => a'
  | some x, some y => if y.2.list.length < x.2.list.length then some y else some x

/-! ## The recursive core -/

variable [DecidableEq Tok]

set_option linter.unusedVariables false in
mutual
  /-- Parse one expression of entry `e` constrained to level `l`. -/
  def parseExpr {G : Grammar Tok} (e : G.Ent) (l : Level (G.entry e)) (tkns : List Tok) :
      Option (Expr G e l × RightSublist tkns) :=
    match l with
    | .loosest =>
        (parseExprList e .loosest (G.entry e).loosest (fun c hc _o hco => ⟨c, hc, hco⟩)
          (fun _ _ => (G.entry e).rank_lt_topRank _) tkns).orElse
          (fun _ => parseVar e .loosest tkns)
    | .tighter a =>
        (parseExprList e (.tighter a) ((G.entry e).tighter a)
          (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco)
          (fun c hc => (G.entry e).rank_tighter a c hc) tkns).orElse
          (fun _ => parseVar e (.tighter a) tkns)
    | .tighterEq a =>
        if hj : ((G.entry e).operator a).isJuxt = true then
          parseJuxt e a (Operator.eq_juxt hj) tkns
        else if hl : ((G.entry e).operator a).isInfxl = true then
          parseInfixL e a hl tkns
        else
          -- longest match, not `orElse`: the fall-through always succeeds when a tighter tree
          -- parses, so preferring the body unconditionally could stop short of it
          let fallthrough : Option (Expr G e (.tighterEq a) × RightSublist tkns) :=
            (parseExpr e (.tighter a) tkns).map
              (fun x => (x.1.reindex (l := .tighter a) (l' := .tighterEq a)
                          (fun _o hh => Tighter.toTighterEq
                            (show Tighter (G.entry e).tighter a _o from hh)), x.2))
          longer
            ((parseParts (Operator.body e a) tkns).map
              (fun x => ((Expr.op a TighterEq.refl x.1 : Expr G e (.tighterEq a)), x.2)))
            fallthrough
  termination_by (tkns.length, Level.measure l, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (partsMeasure_parts_lt _ _ (Operator.leftRec_eq_false hj hl)))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure, Level.base]; omega))

  /-- Walk a level's candidate operators, taking the longest match. -/
  def parseExprList {G : Grammar Tok} (e : G.Ent) (l : Level (G.entry e)) (cs : List (G.entry e).Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq (G.entry e).tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, (G.entry e).rank c < Level.base l)
      (tkns : List Tok) : Option (Expr G e l × RightSublist tkns) :=
    match cs, h, hrank with
    | [], _, _ => none
    | c :: rest, h, hrank =>
        longer
          ((parseExpr e (.tighterEq c) tkns).map
            (fun x => (x.1.reindex (l := .tighterEq c) (l' := l)
                        (fun o hh => h c List.mem_cons_self o
                          (show TighterEq (G.entry e).tighter c o from hh)), x.2)))
          (parseExprList e l rest (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
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

  /-- Parse an operator body `ps` left-to-right. -/
  def parseParts {G : Grammar Tok} : (ps : List (Part G)) → (tkns : List Tok) →
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

  /-- Parse an application chain `f x y …` left-associatively. -/
  def parseJuxt {G : Grammar Tok} (e : G.Ent) (j : (G.entry e).Op)
      (hj : (G.entry e).operator j = Operator.juxt) (tkns : List Tok) :
      Option (Expr G e (Level.tighterEq j) × RightSublist tkns) :=
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
  def parseJuxtExtend {G : Grammar Tok} (e : G.Ent) (j : (G.entry e).Op)
      (hj : (G.entry e).operator j = Operator.juxt)
      (acc : Expr G e (Level.tighterEq j)) (tkns : List Tok) :
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

  /-- Parse a left-associative chain `a ∘ b ∘ c …`. -/
  def parseInfixL {G : Grammar Tok} (e : G.Ent) (o : (G.entry e).Op)
      (hl : ((G.entry e).operator o).isInfxl = true) (tkns : List Tok) :
      Option (Expr G e (Level.tighterEq o) × RightSublist tkns) :=
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
  def parseInfixLExtend {G : Grammar Tok} (e : G.Ent) (o : (G.entry e).Op)
      (hl : ((G.entry e).operator o).isInfxl = true)
      (acc : Expr G e (Level.tighterEq o)) (tkns : List Tok) :
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

end LambdaLab.Parser.IsoParser.Mixfix
