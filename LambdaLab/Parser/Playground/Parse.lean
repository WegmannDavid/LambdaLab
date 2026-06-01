import LambdaLab.Parser.Playground.Tree

/-!
# Precedence-climbing parser (work in progress)

Parses a token stream into a precedence-indexed `Tree`/`Expr`. The shape of the
recursion follows the grammar `⟦a⟧ = (operator a applied) | ⟦tighter a⟧`:

* `parseTree a` parses an expression at node `a`. For a **closed** operator it
  matches the operator's name-parts directly (`parseWoven`); otherwise it falls
  through to a strictly-tighter expression (`parseBelow`, wrapped in `next`).
* **left-associative infix** is handled by `parseInfixLTail`: parse a tighter
  head, then loop folding `op a (infixL acc … R)` for each further occurrence
  (left-nesting).
* `parseWoven` consumes an operator's name-parts, recursing into `parseExpr`
  for the interior (delimited) holes.
* `parseBelow` tries each immediately-tighter node in turn.

Every successful parse returns a `RightSublist` (proper suffix), proving it
consumed ≥1 token — fall-through is fine because it delegates to a parse that
eventually consumes an atom.

## Termination

The recursion has two dimensions, so the measure is the lexicographic
`(tokens, level, list-length)`:

* **tokens** — `tkns.length`; strictly drops whenever a name-part is consumed.
* **level** — built from `Grammar.rank` (a `Nat` manufactured from `tighter_wf`,
  since the abstract graph carries no number): a fall-through descends to a
  strictly tighter node at the *same* tokens, and `rank` strictly drops there.
  The entry parsers sit at `topRank` (above every loosest operator) and
  `parseWoven` at `0` (below every node), so the same-token pipeline
  `parseTree → parseBelow → parseBelowList → parseTree(tighter)` is well-founded.
* **list-length** — the `rs`/`bs` worklists of `parseExprRoots`/`parseBelowList`,
  which shrink while tokens and level stay fixed.

Fully proved — no `sorry`. `prefix`/`postfix`/`infixR`/`infixN` operator
*application* is still stubbed to fall-through only (the `arith` example uses
only closed + left-assoc-infix); extending those is future work.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-! ## A `Nat` rank for the termination measure

The `tighter` graph is well-founded but carries no number, so we manufacture a
`Nat` `rank` that strictly decreases along `tighter`. The parser's termination
measure is then the ordinary lexicographic `(tokens, level, list-length)` with
`level` built from `rank`. -/

/-- Any element of a `Nat` list is `≤` its `foldr max 0`. -/
theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A `Nat` rank derived from the well-founded `tighter` graph: one more than
the max rank of the immediately-tighter operators. Strictly decreasing along
`tighter` (`rank_lt`). Used only to build the parser's termination measure. -/
def Grammar.rank (G : Grammar) (a : G.Op) : Nat :=
  G.tighter_wf.fix (C := fun _ => Nat)
    (fun a ih => ((G.tighter a).attach.map (fun b => ih b.1 b.2 + 1)).foldr Nat.max 0) a

theorem Grammar.rank_eq (G : Grammar) (a : G.Op) :
    G.rank a = ((G.tighter a).attach.map (fun b => G.rank b.1 + 1)).foldr Nat.max 0 :=
  WellFounded.fix_eq _ _ _

/-- The defining property: tighter operators have strictly smaller rank. -/
theorem Grammar.rank_lt (G : Grammar) {a b : G.Op} (h : b ∈ G.tighter a) :
    G.rank b < G.rank a := by
  rw [G.rank_eq a]
  have hmem : G.rank b + 1 ∈ (G.tighter a).attach.map (fun c => G.rank c.1 + 1) :=
    List.mem_map.mpr ⟨⟨b, h⟩, List.mem_attach _ _, rfl⟩
  have := le_foldr_max hmem
  omega

/-- A rank strictly above every loosest operator — the "top" level for the
entry parsers (`parseExpr`/`parseExprRoots`). -/
def Grammar.topRank (G : Grammar) : Nat := (G.loosest.map G.rank).foldr Nat.max 0 + 1

theorem Grammar.rank_lt_topRank (G : Grammar) {r : G.Op} (h : r ∈ G.loosest) :
    G.rank r < G.topRank := by
  have hmem : G.rank r ∈ G.loosest.map G.rank := List.mem_map.mpr ⟨r, h, rfl⟩
  have := le_foldr_max hmem
  unfold Grammar.topRank
  omega

mutual
  /-- Parse a top-level expression: try each loosest root. -/
  def parseExpr (tkns : List Token) : Option (Expr G × RightSublist tkns) :=
    parseExprRoots G.loosest (fun _ h => h) tkns
  termination_by (tkns.length, G.topRank * 4 + 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  /-- Try each root `r ∈ rs ⊆ loosest` in order. -/
  def parseExprRoots (rs : List G.Op) (hsub : ∀ r ∈ rs, r ∈ G.loosest)
      (tkns : List Token) : Option (Expr G × RightSublist tkns) :=
    match rs with
    | [] => none
    | r :: rest =>
        match parseTree r tkns with
        | some (t, rsl) => some (Expr.mk r (hsub r List.mem_cons_self) t, rsl)
        | none => parseExprRoots rest (fun b hb => hsub b (List.mem_cons_of_mem r hb)) tkns
  termination_by (tkns.length, G.topRank * 4 + 1, rs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (by have := G.rank_lt_topRank (hsub r List.mem_cons_self); omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- Parse an expression at precedence node `a`. -/
  def parseTree (a : G.Op) (tkns : List Token) : Option (Tree G a × RightSublist tkns) :=
    match hf : (G.operator a).fixity with
    | .closed =>
        -- `n₀ _ … _ nₖ`: match the name-parts directly, else fall through.
        match parseWoven (G.operator a).nameParts tkns with
        | some (w, r) => some (Tree.op a (hf ▸ Children.closed w), r)
        | none => (parseBelow a tkns).map fun x => (Tree.next x.1, x.2)
    | .prefix =>
        -- `n₀ _ … nₖ _`: name-parts, then a trailing operand at level `a`
        -- (so prefixes stack, e.g. `- - x`).
        match parseWoven (G.operator a).nameParts tkns with
        | some (w, r1) =>
            match parseTree a r1.list with
            | some (t, r2) => some (Tree.op a (hf ▸ Children.prefix w t), r1.trans r2)
            | none => none
        | none => (parseBelow a tkns).map fun x => (Tree.next x.1, x.2)
    | .postfix =>
        -- `_ n₀ _ … nₖ`: left-recursive — parse a tighter head, then loop.
        match parseBelow a tkns with
        | some (first, r0) => some (parsePostfixTail a hf (Tree.next first) tkns r0)
        | none => none
    | .infix .left =>
        -- `_ n₀ _ … _ nₖ _`, left-assoc: tighter head, then a left-folding loop.
        match parseBelow a tkns with
        | some (first, r0) => some (parseInfixLTail a hf (Tree.next first) tkns r0)
        | none => none
    | .infix .right =>
        -- right-assoc: strictly-tighter left, then the trailing operand recurses
        -- at level `a` (right-nesting). No operator following ⇒ just the left.
        match parseBelow a tkns with
        | some (left, r1) =>
            match parseWoven (G.operator a).nameParts r1.list with
            | some (w, r2) =>
                match parseTree a r2.list with
                | some (right, r3) =>
                    some (Tree.op a (hf ▸ Children.infixR left w right), r1.trans (r2.trans r3))
                | none => none
            | none => some (Tree.next left, r1)
        | none => none
    | .infix .nonAssoc =>
        -- non-assoc: both operands strictly tighter, no parens-free chaining.
        match parseBelow a tkns with
        | some (left, r1) =>
            match parseWoven (G.operator a).nameParts r1.list with
            | some (w, r2) =>
                match parseBelow a r2.list with
                | some (right, r3) =>
                    some (Tree.op a (hf ▸ Children.infixN left w right), r1.trans (r2.trans r3))
                | none => none
            | none => some (Tree.next left, r1)
        | none => none
  termination_by (tkns.length, G.rank a * 4 + 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (RightSublist.length_lt _)
      | exact Prod.Lex.left _ _ (by have h1 := r1.length_lt; have h2 := r2.length_lt; omega)

  /-- The left-associative tail loop: fold further occurrences of `a` to the
  left of `acc`. Always succeeds (returns `acc` once no more `a` follows). -/
  def parseInfixLTail (a : G.Op) (hf : (G.operator a).fixity = .infix .left)
      (acc : Tree G a) (tkns0 : List Token) (r : RightSublist tkns0) :
      Tree G a × RightSublist tkns0 :=
    match parseWoven (G.operator a).nameParts r.list with
    | some (w, r1) =>
        match parseBelow a r1.list with
        | some (rt, r2) =>
            parseInfixLTail a hf (Tree.op a (hf ▸ Children.infixL acc w rt)) tkns0
              (r.trans (r1.trans r2))
        | none => (acc, r)
    | none => (acc, r)
  termination_by (r.list.length, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (‹RightSublist r.list›.length_lt)
      | exact Prod.Lex.left _ _
          (by have h1 := r1.length_lt; have h2 := r2.length_lt
              simp only [RightSublist.trans]; omega)

  /-- The postfix tail loop: fold further occurrences of `a` to the left of
  `acc` (`acc !`, `acc ! !`, …). Always succeeds. -/
  def parsePostfixTail (a : G.Op) (hf : (G.operator a).fixity = .postfix)
      (acc : Tree G a) (tkns0 : List Token) (r : RightSublist tkns0) :
      Tree G a × RightSublist tkns0 :=
    match parseWoven (G.operator a).nameParts r.list with
    | some (w, r1) =>
        parsePostfixTail a hf (Tree.op a (hf ▸ Children.postfix acc w)) tkns0 (r.trans r1)
    | none => (acc, r)
  termination_by (r.list.length, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (by have h := r1.length_lt; simp only [RightSublist.trans]; omega)

  /-- Parse something strictly tighter than `a`. -/
  def parseBelow (a : G.Op) (tkns : List Token) : Option (TreeBelow G a × RightSublist tkns) :=
    parseBelowList a (G.tighter a) (fun _ h => h) tkns
  termination_by (tkns.length, G.rank a * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  /-- Try each immediately-tighter node `b ∈ bs ⊆ tighter a`. -/
  def parseBelowList (a : G.Op) (bs : List G.Op) (hsub : ∀ b ∈ bs, b ∈ G.tighter a)
      (tkns : List Token) : Option (TreeBelow G a × RightSublist tkns) :=
    match bs with
    | [] => none
    | b :: rest =>
        match parseTree b tkns with
        | some (t, r) => some (TreeBelow.mk b (hsub b List.mem_cons_self) t, r)
        | none => parseBelowList a rest (fun c hc => hsub c (List.mem_cons_of_mem b hc)) tkns
  termination_by (tkns.length, G.rank a * 4 + 1, bs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (by have := G.rank_lt (hsub b List.mem_cons_self); omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- Consume an operator's name-parts, recursing into `parseExpr` for the
  interior (delimited) holes. -/
  def parseWoven : (parts : List Token) → (tkns : List Token) →
      Option (Woven G parts × RightSublist tkns)
    | [tk], (t :: rest) =>
        if t = tk then some (Woven.last tk, RightSublist.cons t rest) else none
    | (tk :: p :: ps), (t :: rest) =>
        if t = tk then
          match parseExpr rest with
          | some (e, r1) =>
              match parseWoven (p :: ps) r1.list with
              | some (w, r2) =>
                  some (Woven.cons tk e w, (RightSublist.cons t rest).trans (r1.trans r2))
              | none => none
          | none => none
        else none
    | _, _ => none
  termination_by _ tkns => (tkns.length, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.left _ _ (by have := r1.length_lt; omega)
end

/-- Full parse: a top-level expression consuming the entire input. -/
def parse (tkns : List Token) : Option (Expr G) :=
  match parseExpr (G := G) tkns with
  | some (e, r) => if r.list = [] then some e else none
  | none => none

end LambdaLab.Parser.Playground
