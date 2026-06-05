import LambdaLab.Parser.Playground2.Tree

/-!
# Precedence-climbing parser (all parses)

Parses a token stream into **all** precedence-indexed parses: every function
returns a `List (… × RightSublist tkns)` (`none`→`[]`, `some x`→`[x]`,
sequencing→`flatMap`). Roots/nodes are *concatenated*, not first-committed, so
ambiguous or multi-root grammars surface every reading; an unambiguous
(total-order) grammar yields a singleton. `parse` keeps the full-consumption
parses.

The shape of the recursion follows the grammar `⟦a⟧ = (operator a applied) | ⟦tighter a⟧`:

* `parseTree a` parses an expression at node `a`. For a **closed** operator it
  matches the operator's name-parts directly (`parseWoven`); otherwise it falls
  through to a strictly-tighter expression (`parseBelow`, wrapped in `next`).
* All six fixities are handled. `prefix`/infix-`right`/`nonAssoc` are recursive
  descent; the left-recursive `postfix`/infix-`left` use the tail loops
  `parsePostfixTail`/`parseInfixLTail`, which return the stop case `(acc, r)`
  (the fall-through) *and* every further fold — so all prefixes of a spine are
  emitted.
* `parseWoven` consumes an operator's name-parts, recursing into `parseExpr`
  for the interior (delimited) holes.
* `parseBelow` collects parses from every immediately-tighter node.

Every parse in a returned list carries a `RightSublist` (proper suffix), so it
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

Fully proved — no `sorry`. The list rewrite keeps this measure unchanged; the
extra `flatMap`-collected parses don't add recursive calls, only more results,
and each recursive call still decreases the same triple (the `flatMap`-bound
remainder `x.2 : RightSublist …` supplies the token drop via `length_lt`).
-/

namespace LambdaLab.Parser.Playground2

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
  /-- All top-level parses (one per loosest root that succeeds). -/
  def parseExpr (tkns : List Token) : List (Tree G .loosest × RightSublist tkns) :=
    parseExprRoots G.loosest (fun _ h => h) tkns
  termination_by (tkns.length, G.topRank * 4 + 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  /-- Concatenate the parses from every root `r ∈ rs ⊆ loosest` (no first-commit). -/
  def parseExprRoots (rs : List G.Op) (hsub : ∀ r ∈ rs, r ∈ G.loosest)
      (tkns : List Token) : List (Tree G .loosest × RightSublist tkns) :=
    match rs with
    | [] => []
    | r :: rest =>
        (parseTree r tkns).map (fun x =>
          (Tree.reindex (l := Level.tighterEq r) (l' := Level.loosest)
            (fun _ hc => ⟨r, hsub r List.mem_cons_self, hc⟩) x.1, x.2))
        ++ parseExprRoots rest (fun b hb => hsub b (List.mem_cons_of_mem r hb)) tkns
  termination_by (tkns.length, G.topRank * 4 + 1, rs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (by have := G.rank_lt_topRank (hsub r List.mem_cons_self); omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- All parses of an expression at precedence node `a`: operator-`a`
  applications (per fixity) together with fall-throughs to tighter expressions.
  Chaining/stacking is delegated to the spine parsers `parsePrefixStack`,
  `parsePostfixTail`, `parseInfixTail`; the fall-through `Tree.next` is emitted
  alongside. -/
  def parseTree (a : G.Op) (tkns : List Token) : List (Tree G (.tighterEq a) × RightSublist tkns) :=
    match hf : (G.operator a).fixity with
    | .closed =>
        (parseWoven a (G.operator a).nameParts tkns).map
            (fun x => (Tree.opSelf a (hf ▸ Children.closed x.1), x.2))
        ++ (parseBelow a tkns).map (fun x => (x.1.lift, x.2))
    | .prefix =>
        (parsePrefixStack a tkns).map (fun x => (Tree.opSelf a (hf ▸ Children.prefix x.1), x.2))
        ++ (parseBelow a tkns).map (fun x => (x.1.lift, x.2))
    | .postfix =>
        (parseBelow a tkns).flatMap (fun x =>
          (x.1.lift, x.2) ::
          (parsePostfixTail a x.2.list).map (fun y =>
            (Tree.opSelf a (hf ▸ Children.postfix x.1 y.1), x.2.trans y.2)))
    | .infix .left =>
        (parseBelow a tkns).flatMap (fun x =>
          (x.1.lift, x.2) ::
          (parseInfixTail a x.2.list).map (fun y =>
            (Tree.opSelf a (hf ▸ Children.infixL x.1 y.1), x.2.trans y.2)))
    | .infix .right =>
        (parseBelow a tkns).flatMap (fun x =>
          (x.1.lift, x.2) ::
          (parseInfixTail a x.2.list).map (fun y =>
            (Tree.opSelf a (hf ▸ Children.infixR x.1 y.1), x.2.trans y.2)))
    | .infix .nonAssoc =>
        (parseBelow a tkns).flatMap (fun x =>
          (x.1.lift, x.2) ::
          (parseWoven a (G.operator a).nameParts x.2.list).flatMap (fun y =>
            (parseBelow a y.2.list).map (fun z =>
              (Tree.opSelf a (hf ▸ Children.infixN x.1 y.1 z.1), x.2.trans (y.2.trans z.2)))))
  termination_by (tkns.length, G.rank a * 4 + 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; have := y.2.length_lt; omega)

  /-- A non-empty prefix stack: a weave, then either a strictly-tighter body
  (`last`) or a further `a`-prefix layer (`more`). -/
  def parsePrefixStack (a : G.Op) (tkns : List Token) :
      List (Children G a .prefix × RightSublist tkns) :=
    (parseWoven a (G.operator a).nameParts tkns).flatMap (fun x =>
      (parseBelow a x.2.list).map (fun y => (Children.psLast x.1 y.1, x.2.trans y.2))
      ++ (parsePrefixStack a x.2.list).map (fun z => (Children.psMore x.1 z.1, x.2.trans z.2)))
  termination_by (tkns.length, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- A non-empty trailing-weave list for a postfix operator. -/
  def parsePostfixTail (a : G.Op) (tkns : List Token) :
      List (Children G a .postTail × RightSublist tkns) :=
    (parseWoven a (G.operator a).nameParts tkns).flatMap (fun x =>
      (Children.ptLast x.1, x.2) ::
      (parsePostfixTail a x.2.list).map (fun z => (Children.ptCons x.1 z.1, x.2.trans z.2)))
  termination_by (tkns.length, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)

  /-- A non-empty `(separator-weave, tighter operand)` spine for an infix
  operator (shared by left/right associativity). -/
  def parseInfixTail (a : G.Op) (tkns : List Token) :
      List (Children G a .infixTail × RightSublist tkns) :=
    (parseWoven a (G.operator a).nameParts tkns).flatMap (fun x =>
      (parseBelow a x.2.list).flatMap (fun y =>
        (Children.itLast x.1 y.1, x.2.trans y.2) ::
        (parseInfixTail a y.2.list).map (fun z =>
          (Children.itCons x.1 y.1 z.1, x.2.trans (y.2.trans z.2)))))
  termination_by (tkns.length, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; have := y.2.length_lt; omega)

  /-- All strictly-tighter parses. -/
  def parseBelow (a : G.Op) (tkns : List Token) : List (Tree G (.tighter a) × RightSublist tkns) :=
    parseBelowList a (G.tighter a) (fun _ h => h) tkns
  termination_by (tkns.length, G.rank a * 4 + 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  /-- Concatenate the parses from every immediately-tighter node `b ∈ bs`. -/
  def parseBelowList (a : G.Op) (bs : List G.Op) (hsub : ∀ b ∈ bs, b ∈ G.tighter a)
      (tkns : List Token) : List (Tree G (.tighter a) × RightSublist tkns) :=
    match bs with
    | [] => []
    | b :: rest =>
        (parseTree b tkns).map (fun x =>
          (Tree.reindex (l := Level.tighterEq b) (l' := Level.tighter a)
            (fun _ hc => tighter_of_mem_tighterEq (hsub b List.mem_cons_self) hc) x.1, x.2))
        ++ parseBelowList a rest (fun c hc => hsub c (List.mem_cons_of_mem b hc)) tkns
  termination_by (tkns.length, G.rank a * 4 + 1, bs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (by have := G.rank_lt (hsub b List.mem_cons_self); omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- Consume an operator's name-parts, recursing into `parseExpr` for the
  interior (delimited) holes. -/
  def parseWoven (a : G.Op) : (parts : List Token) → (tkns : List Token) →
      List (Children G a (.weave parts) × RightSublist tkns)
    | [tk], (t :: rest) =>
        if t = tk then [(Children.wLast tk, RightSublist.cons t rest)] else []
    | (tk :: p :: ps), (t :: rest) =>
        if t = tk then
          (parseExpr rest).flatMap (fun x =>
            (parseWoven a (p :: ps) x.2.list).map (fun y =>
              (Children.wCons tk x.1 y.1, (RightSublist.cons t rest).trans (x.2.trans y.2))))
        else []
    | _, _ => []
  termination_by _ tkns => (tkns.length, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.left _ _ (by have := x.2.length_lt; omega)
end

/-- All full parses (consuming the entire input). For an unambiguous grammar
this is a singleton (or empty). -/
def parse (tkns : List Token) : List (Tree G .loosest) :=
  (parseExpr (G := G) tkns).filterMap (fun x => if x.2.list = [] then some x.1 else none)

end LambdaLab.Parser.Playground2
