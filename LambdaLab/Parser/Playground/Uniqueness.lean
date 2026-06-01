import LambdaLab.Parser.Playground.Completeness

/-!
# Uniqueness: when does `parse` return at most one result?

`parse` returns a *list* of all full parses. It returns "at most one result"
(all returned expressions are equal) **iff** the grammar is unambiguous, i.e.
`flatten` is injective on `Expr G`. That equivalence has a cheap half and a
hard half:

* **Cheap (`parse_unique`)**: `FlattenInjective G → parse` is subsingleton.
  Immediate from soundness — the parser invents no parse beyond the genuine
  tree ambiguity, so two results have equal flatten, hence are equal.
* **Hard (`unambiguous_flatten_injective`)**: a *checkable syntactic* criterion
  `Unambiguous G` (distinct name tokens + forest-shaped precedence) implies
  `FlattenInjective G`. This is the substantial direction (mutual tree
  induction); the concrete grammars then discharge `Unambiguous` by `cases`.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-- A grammar is **unambiguous** when `flatten` is injective on top-level
expressions: no two distinct trees flatten to the same token string. -/
def FlattenInjective (G : Grammar) : Prop :=
  ∀ e₁ e₂ : Expr G, e₁.flatten = e₂.flatten → e₁ = e₂

/-- If the grammar is unambiguous, `parse` yields at most one result: any two
expressions it returns are equal. (Immediate from soundness — both flatten to
`tkns`.) -/
theorem parse_unique (hG : FlattenInjective G) {tkns : List Token} {e₁ e₂ : Expr G}
    (h₁ : e₁ ∈ parse (G := G) tkns) (h₂ : e₂ ∈ parse (G := G) tkns) : e₁ = e₂ :=
  hG e₁ e₂ ((mem_parse_iff.mp h₁).trans (mem_parse_iff.mp h₂).symm)

/-! ## A checkable sufficient criterion for unambiguity

`Unambiguous G` bundles the two syntactic conditions that rule out all three
ambiguity sources:

* distinct name tokens (`nameParts_nodup` + `nameParts_disjoint`) — handles the
  intra-operator split and the operator-vs-fall-through cases;
* forest-shaped precedence (`tighter_disjoint` + `loosest_disjoint`: distinct
  immediate-tighter siblings, and distinct roots, have disjoint reachable sets)
  — handles the fall-through *path* (diamond) and multi-root cases.

It is decidable on a concrete grammar (`cases` on `Op`), strictly more general
than requiring a total order (it admits `arith`'s branching `mul → {paren,num}`),
and sufficient for `FlattenInjective`. -/
structure Unambiguous (G : Grammar) : Prop where
  nameParts_nodup : ∀ a : G.Op, (G.operator a).nameParts.Nodup
  nameParts_disjoint : ∀ a b : G.Op, a ≠ b →
    ∀ tk ∈ (G.operator a).nameParts, tk ∉ (G.operator b).nameParts
  tighter_disjoint : ∀ (a b₁ b₂ : G.Op), b₁ ∈ G.tighter a → b₂ ∈ G.tighter a → b₁ ≠ b₂ →
    ∀ c, ReachTighter G.tighter b₁ c → ReachTighter G.tighter b₂ c → False
  loosest_disjoint : ∀ (r₁ r₂ : G.Op), r₁ ∈ G.loosest → r₂ ∈ G.loosest → r₁ ≠ r₂ →
    ∀ c, ReachTighter G.tighter r₁ c → ReachTighter G.tighter r₂ c → False

/-- A sink (`tighter a = []`) reaches only itself — inverting `ReachTighter`. -/
theorem ReachTighter.eq_of_sink {t : G.Op → List G.Op} {a c : G.Op}
    (hsink : t a = []) (h : ReachTighter t a c) : c = a := by
  cases h with
  | refl => rfl
  | step hmem _ => rw [hsink] at hmem; exact absurd hmem List.not_mem_nil

/-- `ReachTighter` is transitive — composing two tighter-paths. -/
theorem ReachTighter.trans {t : G.Op → List G.Op} {a b c : G.Op}
    (h₁ : ReachTighter t a b) (h₂ : ReachTighter t b c) : ReachTighter t a c := by
  induction h₁ with
  | refl => exact h₂
  | step hmem _ ih => exact ReachTighter.step hmem (ih h₂)

/-! ## Structural building blocks for `unambiguous_flatten_injective`

These mutual structural lemmas hold for *any* grammar and are the scaffolding the
hard direction is built on. `*_flatten_ne` (flatten is never empty) is needed to
land the leading-token argument; it is fully proved. -/

mutual
  /-- A `Tree`'s flatten is never empty. -/
  theorem Tree.flatten_ne {b : G.Op} (t : Tree G b) : t.flatten ≠ [] := by
    match t with
    | .op _ ch => simpa only [Tree.flatten] using ch.flatten_ne
    | .next tb => simpa only [Tree.flatten] using tb.flatten_ne

  /-- A `TreeBelow`'s flatten is never empty. -/
  theorem TreeBelow.flatten_ne {b : G.Op} (t : TreeBelow G b) : t.flatten ≠ [] := by
    match t with
    | .mk _ _ tc => simpa only [TreeBelow.flatten] using tc.flatten_ne

  /-- A `Children`'s flatten is never empty (the operator's name-parts are
  non-empty, so even a `closed` node emits at least one token). -/
  theorem Children.flatten_ne {b : G.Op} {f : Fixity} (ch : Children G b f) :
      ch.flatten ≠ [] := by
    match ch with
    | .closed w => simpa only [Children.flatten] using w.flatten_ne
    | .prefix w _ =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .postfix t _ =>
        simp only [Children.flatten]; intro h
        exact t.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .infixL l _ _ =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
    | .infixR l _ _ =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
    | .infixN l _ _ =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1

  /-- A `Woven`'s flatten is never empty. -/
  theorem Woven.flatten_ne {parts : List Token} (w : Woven G parts) : w.flatten ≠ [] := by
    match w with
    | .last _ => simp [Woven.flatten]
    | .cons _ _ _ => simp [Woven.flatten]
end

/-- **The hard direction (open).** The syntactic criterion implies unambiguity.

The intended route is a single mutual induction over the tree family proving a
*unique-decomposition* (prefix) statement, e.g. for `Tree`:

  `t₁.flatten ++ s₁ = t₂.flatten ++ s₂ → t₁ = t₂ ∧ s₁ = s₂`

(and the analogues for `TreeBelow`/`Children`/`Woven`/`Expr`). The plain
equality form does not self-support — splitting an append like
`l.flatten ++ w.flatten ++ r.flatten` needs the operand boundaries to be
*forced*, which is precisely a prefix-freeness fact, so the statement must be
strengthened to the decomposition form above before the induction closes.

Scaffolding in place: `Tree.flatten_ne` et al. (flatten non-empty) and
`ReachTighter.trans`. The blocking sub-lemma is the leading-token discrimination
for `op` vs `next`:

  a node `a`'s own head token (`(G.operator a).head`) cannot occur as the leading
  token of any *strictly tighter* expression's flatten.

This needs (i) a head-token-reachability lemma — the leading token of
`t : Tree G b` is a name-part of some operator `o` with `ReachTighter tighter b o`
(and for the interior `Woven` holes, the delimiter name-parts bound the split) —
and (ii) acyclicity of `tighter` (`tighter_wf`) to show `a` is not reachable from
a `b ∈ tighter a`, so by `nameParts_disjoint` the token differs. The
`tighter_disjoint`/`loosest_disjoint` forest fields then rule out the remaining
`next` vs `next` (distinct-node) and multi-root cases. This is the mixfix
unique-decomposition theorem; it remains open here. -/
theorem unambiguous_flatten_injective (hG : Unambiguous G) : FlattenInjective G := by
  sorry

end LambdaLab.Parser.Playground
