import LambdaLab.Parser.Mixfix.Tree

/-!
# Parser for the `Part`/`Parts` parse-tree model (all parses)

A precedence-climbing parser over the flattened operator-body representation of
`Tree.lean`: an operator body is a `List (Part G)`, each `Part` either a literal
`namePart` token or a recursive `hole` at some precedence `Level`. The parser
returns **all** precedence-indexed parses (`List (… × RightSublist tkns)`,
concatenated, never first-committed), so an ambiguous or multi-root grammar
surfaces every reading and an unambiguous one yields a singleton.

The recursion mirrors the level structure `condition`:

* `parseExpr .loosest` / `parseExpr (.tighter a)` fan out, via `parseExprList`,
  over the candidate operator lists (`G.loosest` / `G.tighter a`), reindexing
  each `Tree G (.tighterEq c)` up to the requested level.
* `parseExpr (.tighterEq a)` either applies operator `a` itself (parsing its
  body `Part.parts a` with `parseParts`) or falls through to a strictly-tighter
  expression.
* `parseParts` walks an operator body left-to-right: a `namePart` must match the
  next token; a `hole` recurses into `parseExpr` at the hole's level.

The parser is **total** — defined by well-founded recursion on the lexicographic
triple `(tkns.length, levelMeasure, list-length)`:

* **tokens** — `tkns.length`; drops whenever a `namePart` is matched or a hole's
  sub-expression is consumed (a `RightSublist`).
* **levelMeasure** — `rank · 4 + phase`, where `rank` is a `Nat` manufactured
  from `tighter_wf` (`Grammar.rank`, strictly decreasing along `tighter`). At
  *equal* tokens the chain `tighterEq a → body a → tighter a → tighterEq b`
  (`b ∈ tighter a`) strictly decreases: the phases order the first three steps,
  and `rank b < rank a` drops the last. The leading-hole recursion of an infix
  operator (whose body `Part.parts a` begins with `.hole (.tighter a)`) is the
  only same-token descent into a sub-expression, and it drops `rank`.
* **list-length** — the candidate worklist of `parseExprList`, shrinking while
  tokens and level stay fixed.

No correctness proofs (soundness / completeness / uniqueness) — only termination.
-/

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

variable {G : Grammar}

/-! ## Precedence-order plumbing -/

/-- A `tighter`-or-equal path is either trivial or a strictly-tighter path. -/
theorem TighterEq.toTighterOrEq {Op : Type} {t : Op → List Op} {a b : Op}
    (h : TighterEq t a b) : a = b ∨ Tighter t a b := by
  induction h with
  | refl => exact Or.inl rfl
  | step hmem _ ih =>
      cases ih with
      | inl hEq => exact Or.inr (hEq ▸ Tighter.base hmem)
      | inr hT  => exact Or.inr (Tighter.step hmem hT)

/-- Prepending an immediate `tighter` step to a `tighter`-or-equal path yields a
*strictly* tighter path: the witness that an operator reached from `b ∈ tighter a`
binds strictly more tightly than `a`. -/
theorem Tighter.ofMemTighterEq {Op : Type} {t : Op → List Op} {a b o : Op}
    (hmem : b ∈ t a) (h : TighterEq t b o) : Tighter t a o := by
  cases h.toTighterOrEq with
  | inl hEq => exact hEq ▸ Tighter.base hmem
  | inr hT  => exact Tighter.step hmem hT

/-- Weaken the level of an expression along an implication of level conditions.
Since `Expr.op` stores the operator (not the level), only the level witness
changes — the body and hence the flattening are untouched. -/
def Expr.reindex {l l' : Level G}
    (h : ∀ o, Level.condition l o → Level.condition l' o) : Expr G l → Expr G l'
  | .op o hc parts => .op o (h o hc) parts
  | .var t hv => .var t hv

/-! ## A `Nat` rank for the termination measure

The `tighter` graph is well-founded but carries no number, so we manufacture a
`Nat` `rank` strictly decreasing along `tighter`, exactly as in the other
playgrounds. -/

/-- Any element of a `Nat` list is `≤` its `foldr max 0`. -/
theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A `Nat` rank derived from the well-founded `tighter` graph: one more than the
max rank of the immediately-tighter operators. Strictly decreasing along
`tighter` (`rank_lt`). -/
def Grammar.rank (G : Grammar) (a : G.Op) : Nat :=
  G.tighter_wf.fix (C := fun _ => Nat)
    (fun a ih => ((G.tighter a).attach.map (fun b => ih b.1 b.2 + 1)).foldr Nat.max 0) a

theorem Grammar.rank_eq (G : Grammar) (a : G.Op) :
    G.rank a = ((G.tighter a).attach.map (fun b => G.rank b.1 + 1)).foldr Nat.max 0 :=
  WellFounded.fix_eq _ _ _

/-- Tighter operators have strictly smaller rank. -/
theorem Grammar.rank_lt (G : Grammar) {a b : G.Op} (h : b ∈ G.tighter a) :
    G.rank b < G.rank a := by
  rw [G.rank_eq a]
  have hmem : G.rank b + 1 ∈ (G.tighter a).attach.map (fun c => G.rank c.1 + 1) :=
    List.mem_map.mpr ⟨⟨b, h⟩, List.mem_attach _ _, rfl⟩
  have := le_foldr_max hmem
  omega

/-- A rank strictly above every loosest operator. -/
def Grammar.topRank (G : Grammar) : Nat := (G.loosest.map G.rank).foldr Nat.max 0 + 1

theorem Grammar.rank_lt_topRank (G : Grammar) {r : G.Op} (h : r ∈ G.loosest) :
    G.rank r < G.topRank := by
  have hmem : G.rank r ∈ G.loosest.map G.rank := List.mem_map.mpr ⟨r, h, rfl⟩
  have := le_foldr_max hmem
  unfold Grammar.topRank
  omega

/-- The looseness base of a level: `topRank` for `loosest`, the operator's rank
for `tighter`/`tighterEq`. Used as the candidate-worklist's measure. -/
def Level.base : Level G → Nat
  | .loosest     => G.topRank
  | .tighter a   => G.rank a
  | .tighterEq a => G.rank a

/-- The secondary termination measure of a level: `base · 4 + phase`. The phase
orders, at equal tokens, the same-rank chain `tighterEq → body → tighter`
(`tighterEq` is `3`; `loosest`/`tighter`, which only fan out, are `1`). -/
def Level.measure : Level G → Nat
  | .loosest     => G.topRank * 4 + 1
  | .tighter a   => G.rank a * 4 + 1
  | .tighterEq a => G.rank a * 4 + 3

/-- The secondary measure of an operator body: one more than the leading hole's
level measure (so parsing that hole strictly decreases), or `0` when the body
starts with a `namePart` (which consumes a token instead). -/
def partsMeasure : List (Part G) → Nat
  | .hole ℓ :: _ => Level.measure ℓ + 1
  | _            => 0

/-- An operator body's `Part.inner` segment always begins with a `namePart`, so
it carries no leading-hole measure. -/
theorem partsMeasure_inner_eq_zero (tkns : NonEmptyList Token) :
    partsMeasure (Part.inner (G := G) tkns) = 0 := by
  cases tkns <;> rfl

/-- The **left-recursive** operators — body leads with a `.tighterEq` operand
hole — which `parseParts` cannot handle (no token is consumed before recursing):
juxtaposition and left-associative infix. Parsed by a fold instead. -/
def Operator.leftRec : Operator → Bool
  | .juxt    => true
  | .infxl _ => true
  | _        => false

/-- An operator body measures strictly below its own `tighterEq` level: a
`closed` or `prefx` body starts with a `namePart` (measure `0`); an `infx` or
`postfx` body starts with `.hole (.tighter a)` (measure `rank a · 4 + 2`), all
`< rank a · 4 + 3`. -/
theorem partsMeasure_parts_lt (a : G.Op) (hne : (G.operator a).leftRec = false) :
    partsMeasure (Part.parts a) < Level.measure (Level.tighterEq a) := by
  unfold Part.parts
  cases h : G.operator a with
  | closed tkns =>
      rw [partsMeasure_inner_eq_zero]
      simp only [Level.measure]; omega
  | prefx tkns =>
      have hz : partsMeasure (Part.inner (G := G) tkns ++ [.hole (.tighter a)]) = 0 := by
        cases tkns <;> rfl
      rw [hz]
      simp only [Level.measure]; omega
  | infx tkns =>
      simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]
      omega
  | infxl tkns => rw [h, Operator.leftRec] at hne; exact absurd hne (by simp)
  | infxr tkns =>
      simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]
      omega
  | juxt => rw [h, Operator.leftRec] at hne; exact absurd hne (by simp)
  | postfx tkns =>
      simp only [List.cons_append, List.nil_append, partsMeasure, Level.measure]
      omega

/-- Parse a single variable leaf: if the next token is an identifier (`isVar`),
emit `Expr.var` at the requested level (variables are valid atoms everywhere).
Non-recursive, so it is termination-neutral wherever it is appended. -/
def parseVar (l : Level G) : (tkns : List Token) → List (Expr G l × RightSublist tkns)
  | [] => []
  | t :: rest =>
      if h : G.isVar t = true then [(Expr.var t h, RightSublist.cons t rest)] else []

/-- The body of a juxtaposition operator: a left operand (at `.tighterEq`, so it
chains left-associatively) and an argument (at `.tighter`). No name tokens. -/
theorem Part.parts_juxt {j : G.Op} (hj : G.operator j = Operator.juxt) :
    Part.parts j = [Part.hole (Level.tighterEq j), Part.hole (Level.tighter j)] := by
  unfold Part.parts; rw [hj]

/-- Smart constructor for one application node `f x` (`Expr.op` over the
juxtaposition operator `j`), hiding the dependent-`Part.parts` cast. -/
def Expr.juxtApp {j : G.Op} (hj : G.operator j = Operator.juxt)
    (f : Expr G (Level.tighterEq j)) (x : Expr G (Level.tighter j)) : Expr G (Level.tighterEq j) :=
  Expr.op j TighterEq.refl ((Part.parts_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil))

/-- A `Bool` test for the juxtaposition operator (avoids needing `DecidableEq Op`). -/
def Operator.isJuxt : Operator → Bool
  | .juxt => true
  | _     => false

theorem Operator.eq_juxt {o : Operator} (h : o.isJuxt = true) : o = Operator.juxt := by
  cases o <;> simp_all [Operator.isJuxt]

theorem Operator.ne_juxt {o : Operator} (h : ¬ (o.isJuxt = true)) : o ≠ Operator.juxt :=
  fun he => h (by rw [he]; rfl)

/-- A `Bool` test for left-associative infix. -/
def Operator.isInfxl : Operator → Bool
  | .infxl _ => true
  | _        => false

/-- Left-assoc and juxtaposition are distinct shapes. -/
theorem Operator.not_isJuxt_of_isInfxl {o : Operator} (h : o.isInfxl = true) :
    o.isJuxt = false := by cases o <;> simp_all [Operator.isInfxl, Operator.isJuxt]

/-- Neither juxt nor left-assoc ⇒ not left-recursive (so `parseParts` applies). -/
theorem Operator.leftRec_eq_false {o : Operator}
    (hj : ¬ o.isJuxt = true) (hl : ¬ o.isInfxl = true) : o.leftRec = false := by
  cases o <;> simp_all [Operator.isJuxt, Operator.isInfxl, Operator.leftRec]

/-- A left-assoc body splits as its (chaining) left operand hole and the tail
(operator tokens + strictly-tighter right operand). -/
theorem Part.parts_infxl_cons {o : G.Op} (hl : (G.operator o).isInfxl = true) :
    Part.parts o = Part.hole (Level.tighterEq o) :: (Part.parts o).tail := by
  cases hop : G.operator o with
  | infxl tkns => unfold Part.parts; rw [hop]; rfl
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- The tail of a left-assoc body leads with a name token, so it consumes one
before recursing (`partsMeasure = 0`) — the fold's termination. -/
theorem partsMeasure_infxl_tail {o : G.Op} (hl : (G.operator o).isInfxl = true) :
    partsMeasure (Part.parts o).tail = 0 := by
  cases hop : G.operator o with
  | infxl tkns => unfold Part.parts; rw [hop]; cases tkns <;> rfl
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- Smart constructor for one left-assoc fold step `(acc) ∘ rhs` (`Expr.op` over a
left-assoc operator `o`), hiding the dependent-`Part.parts` cast. -/
def Expr.infxlApp {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (acc : Expr G (Level.tighterEq o)) (tail : Parts G (Part.parts o).tail) :
    Expr G (Level.tighterEq o) :=
  Expr.op o TighterEq.refl ((Part.parts_infxl_cons hl).symm ▸ Parts.hole acc tail)

/-! ## The parser -/

-- A couple of `decreasing_by` leaves unfold the level measures with a fixed
-- `simp only` set whose lemmas don't all fire on every goal; that's intended.
set_option linter.unusedSimpArgs false in
mutual
  /-- All parses of an expression constrained to level `l`. -/
  def parseExpr : (l : Level G) → (tkns : List Token) →
      List (Expr G l × RightSublist tkns)
    | .loosest, tkns =>
        parseExprList .loosest G.loosest (fun c hc _o hco => ⟨c, hc, hco⟩)
          (fun _ hc => G.rank_lt_topRank hc) tkns
        ++ parseVar .loosest tkns
    | .tighter a, tkns =>
        parseExprList (.tighter a) (G.tighter a) (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco)
          (fun _ hc => G.rank_lt hc) tkns
        ++ parseVar (.tighter a) tkns
    | .tighterEq a, tkns =>
        if hj : (G.operator a).isJuxt = true then
          parseJuxt a (Operator.eq_juxt hj) tkns
        else if hl : (G.operator a).isInfxl = true then
          parseInfixL a hl tkns
        else
          (parseParts (Part.parts a) tkns).map
              (fun x => ((Expr.op a TighterEq.refl x.1 : Expr G (.tighterEq a)), x.2))
          ++ (parseExpr (.tighter a) tkns).map
              (fun x => (x.1.reindex (l := .tighter a) (l' := .tighterEq a)
                          (fun _ hh => Tighter.toTighterEq (show Tighter G.tighter a _ from hh)), x.2))
  termination_by l tkns => (tkns.length, Level.measure l, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (partsMeasure_parts_lt _ (Operator.leftRec_eq_false (by assumption) (by assumption))))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure, Level.base]; omega))

  /-- Concatenate, with no first-commit, the parses contributed by each candidate
  operator `c ∈ cs`: parse at `c`'s own level and reindex up to `l`. `h` supplies,
  per candidate, the proof that anything `c` reaches satisfies level `l`; `hrank`
  the rank bound that makes the candidate descent decrease. -/
  def parseExprList (l : Level G) (cs : List G.Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq G.tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, G.rank c < Level.base l) :
      (tkns : List Token) → List (Expr G l × RightSublist tkns) :=
    fun tkns =>
      match cs, h, hrank with
      | [], _, _ => []
      | c :: rest, h, hrank =>
          (parseExpr (.tighterEq c) tkns).map
              (fun x => (x.1.reindex (l := .tighterEq c) (l' := l)
                          (fun o hh => h c List.mem_cons_self o
                            (show TighterEq G.tighter c o from hh)), x.2))
          ++ parseExprList l rest (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
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

  /-- Parse an operator body `ps : List (Part G)` left-to-right: match each
  `namePart` against the next token, recurse into `parseExpr` at each `hole`'s
  level. The two singleton cases bottom out the recursion without a separate
  empty-consuming step, so every result consumes ≥1 token (a `RightSublist`). -/
  def parseParts : (ps : List (Part G)) → (tkns : List Token) →
      List (Parts G ps × RightSublist tkns)
    | [], _ => []
    | [.namePart tk], tkns =>
        match tkns with
        | t :: rest => if t = tk then [(Parts.namePart tk Parts.nil, RightSublist.cons t rest)] else []
        | []        => []
    | [.hole l], tkns =>
        (parseExpr l tkns).map (fun x => (Parts.hole x.1 Parts.nil, x.2))
    | .namePart tk :: y :: rest', tkns =>
        match tkns with
        | t :: ts =>
            if t = tk then
              (parseParts (y :: rest') ts).map
                  (fun z => (Parts.namePart tk z.1, (RightSublist.cons t ts).trans z.2))
            else []
        | [] => []
    | .hole l :: y :: rest', tkns =>
        (parseExpr l tkns).flatMap (fun x =>
          (parseParts (y :: rest') x.2.list).map
              (fun z => (Parts.hole x.1 z.1, x.2.trans z.2)))
  termination_by ps tkns => (tkns.length, partsMeasure ps, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by first | (simp only [partsMeasure]; omega) | omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)
      | exact Prod.Lex.left _ _ (by first | (simp only [List.length_cons]; omega) | omega)

  /-- Parse an application chain `f x y …` **left-associatively by iteration** (not
  left recursion): parse the leftmost atom at `.tighter j`, then fold further atoms
  onto it. Returns every chain-prefix with its leftover, like the rest of the parser.
  Sits at measure `rank j * 4 + 2`, between `.tighter j` (`+1`) and `.tighterEq j`
  (`+3`), so the same-token descent into the leftmost atom strictly decreases. -/
  def parseJuxt (j : G.Op) (hj : G.operator j = Operator.juxt) :
      (tkns : List Token) → List (Expr G (Level.tighterEq j) × RightSublist tkns) :=
    fun tkns =>
      (parseExpr (Level.tighter j) tkns).flatMap (fun x =>
        let lone : Expr G (Level.tighterEq j) :=
          x.1.reindex (l := Level.tighter j) (l' := Level.tighterEq j)
            (fun _o hh => Tighter.toTighterEq (show Tighter G.tighter j _o from hh))
        (lone, x.2) :: (parseJuxtExtend j hj lone x.2.list).map (fun y => (y.1, x.2.trans y.2)))
  termination_by tkns => (tkns.length, G.rank j * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- Fold one more argument atom onto an application accumulator, then recurse. -/
  def parseJuxtExtend (j : G.Op) (hj : G.operator j = Operator.juxt)
      (acc : Expr G (Level.tighterEq j)) :
      (tkns : List Token) → List (Expr G (Level.tighterEq j) × RightSublist tkns) :=
    fun tkns =>
      (parseExpr (Level.tighter j) tkns).flatMap (fun x =>
        let acc' : Expr G (Level.tighterEq j) := Expr.juxtApp hj acc x.1
        (acc', x.2) :: (parseJuxtExtend j hj acc' x.2.list).map (fun y => (y.1, x.2.trans y.2)))
  termination_by tkns => (tkns.length, G.rank j * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- Parse a left-associative chain `a ∘ b ∘ c …` by iteration (not left
  recursion): parse the leftmost operand at `.tighter o`, then fold further
  `∘ rhs` segments. Mirrors `parseJuxt`; sits at the same measure `rank o * 4 + 2`. -/
  def parseInfixL (o : G.Op) (hl : (G.operator o).isInfxl = true) :
      (tkns : List Token) → List (Expr G (Level.tighterEq o) × RightSublist tkns) :=
    fun tkns =>
      (parseExpr (Level.tighter o) tkns).flatMap (fun x =>
        let lone : Expr G (Level.tighterEq o) :=
          x.1.reindex (l := Level.tighter o) (l' := Level.tighterEq o)
            (fun _o hh => Tighter.toTighterEq (show Tighter G.tighter o _o from hh))
        (lone, x.2) :: (parseInfixLExtend o hl lone x.2.list).map (fun y => (y.1, x.2.trans y.2)))
  termination_by tkns => (tkns.length, G.rank o * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Level.measure]; omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- Fold one more `∘ rhs` segment onto a left-assoc accumulator, then recurse.
  The segment is the body tail (operator tokens + right operand at `.tighter o`),
  parsed by `parseParts`; it leads with a name token, so it consumes ≥1 token. -/
  def parseInfixLExtend (o : G.Op) (hl : (G.operator o).isInfxl = true)
      (acc : Expr G (Level.tighterEq o)) :
      (tkns : List Token) → List (Expr G (Level.tighterEq o) × RightSublist tkns) :=
    fun tkns =>
      (parseParts (Part.parts o).tail tkns).flatMap (fun tp =>
        let acc' : Expr G (Level.tighterEq o) := Expr.infxlApp hl acc tp.1
        (acc', tp.2) :: (parseInfixLExtend o hl acc' tp.2.list).map (fun y => (y.1, tp.2.trans y.2)))
  termination_by tkns => (tkns.length, G.rank o * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by rw [partsMeasure_infxl_tail hl]; omega))
      | exact Prod.Lex.left _ _ (by have := tp.2.length_lt; omega)
end

/-- All full parses (consuming the entire input). For an unambiguous grammar
this is a singleton (or empty). -/
def parse (tkns : List Token) : List (Expr G .loosest) :=
  (parseExpr (G := G) .loosest tkns).filterMap (fun x => if x.2.list = [] then some x.1 else none)

end LambdaLab.Parser.Mixfix
