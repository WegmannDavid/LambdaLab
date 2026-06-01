import LambdaLab.Parser.Playground.Soundness

/-!
# Completeness / round-trip of the closed-operator parser

The converse of soundness: every tree's flattening parses back to that tree.
This is where the grammar's `lookup_spec` well-formedness is needed — it is
what lets `parseTree` recover the operator from the leading token.

* `parseTree_complete  : (parseTree (t.flatten ++ rest)).map (·.1, ·.2.list) = some (t, rest)`
* `parseChildren_complete` : the analogue threading an `OpDesc`
* `parseAll_complete   : parseAll (parser G) t.flatten = some t`

and the headline consequences

* `flatten_injective : t₁.flatten = t₂.flatten → t₁ = t₂`  (unambiguity)
* `parse_iff         : parseAll (parser G) tkns = some t ↔ t.flatten = tkns`

Statements use the `.list` projection of the remainder rather than the raw
`RightSublist` (whose `pre` data field makes value-equality too strong).
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

/-- The leading token of an operator's shape. -/
def OpDesc.head : OpDesc n → Token
  | .part t _ => t
  | .last t => t

@[simp] theorem beginsWith_head (d : OpDesc n) : beginsWith d d.head = true := by
  cases d <;> simp [beginsWith, OpDesc.head]

/-- A flattened child list starts with its driving `OpDesc`'s leading token. -/
theorem Children.flatten_eq {G : Grammar} {n : Nat} (d : OpDesc n) (cs : Children G n) :
    ∃ tl, Children.flatten d cs = d.head :: tl := by
  cases d with
  | last t => cases cs; exact ⟨[], by simp [Children.flatten, OpDesc.head]⟩
  | part t d' =>
    cases cs with
    | part child cs' =>
      exact ⟨child.flatten ++ Children.flatten d' cs', by simp [Children.flatten, OpDesc.head]⟩

/-- `lookup` resolves an operator's leading token back to that operator. -/
theorem lookup_head {G : Grammar} (o : G.Op) : G.lookup (G.OpDescs o).head = some o :=
  (G.lookup_spec o (G.OpDescs o).head).mp (beginsWith_head (G.OpDescs o))

/-- `parseChildren` on a `.last t` whose input starts with `t`. -/
theorem parseChildren_last {G : Grammar} (t : Token) (rest : List Token) :
    parseChildren (G := G) (.last t) (t :: rest) = some (Children.last, RightSublist.cons t rest) := by
  simp [parseChildren]

/-- `parseTree` on a node flattening delegates to `parseChildren` on the
operator's shape: the leading token (recovered via `lookup_spec`) selects `o`. -/
theorem parseTree_node {G : Grammar} (o : G.Op) (cs : Children G (G.arity o)) (rest : List Token) :
    parseTree (Children.flatten (G.OpDescs o) cs ++ rest)
      = (parseChildren (G.OpDescs o) (Children.flatten (G.OpDescs o) cs ++ rest)).map
          (fun x => (Tree.op o x.1, x.2)) := by
  obtain ⟨tl, hF⟩ := Children.flatten_eq (G.OpDescs o) cs
  rw [hF, List.cons_append]
  simp only [parseTree, lookup_head]

mutual
  theorem parseTree_complete {G : Grammar} :
      (t : Tree G) → (rest : List Token) →
      (parseTree (t.flatten ++ rest)).map (fun x => (x.1, x.2.list)) = some (t, rest)
    | .op o cs, rest => by
      obtain ⟨⟨cs2, r2⟩, hpc, heq⟩ :=
        Option.map_eq_some_iff.mp (parseChildren_complete (G.OpDescs o) cs rest)
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, hrest⟩ := heq
      simp only [Tree.flatten, parseTree_node, Option.map_map, Function.comp_def]
      rw [hpc]
      simp [hrest]

  theorem parseChildren_complete {G : Grammar} :
      {n : Nat} → (d : OpDesc n) → (cs : Children G n) → (rest : List Token) →
      (parseChildren d (Children.flatten d cs ++ rest)).map (fun x => (x.1, x.2.list)) = some (cs, rest)
    | _, .last t, .last, rest => by
      simp only [Children.flatten, List.singleton_append]
      rw [parseChildren_last]
      simp [RightSublist.cons]
    | _, .part t d', .part child cs', rest => by
      obtain ⟨⟨child2, r'⟩, hpt, heqt⟩ :=
        Option.map_eq_some_iff.mp (parseTree_complete child (Children.flatten d' cs' ++ rest))
      simp only [Prod.mk.injEq] at heqt
      obtain ⟨rfl, hr'⟩ := heqt
      obtain ⟨⟨cs2, r2⟩, hpc, heqc⟩ :=
        Option.map_eq_some_iff.mp (parseChildren_complete d' cs' rest)
      simp only [Prod.mk.injEq] at heqc
      obtain ⟨rfl, hr2⟩ := heqc
      have hin : Children.flatten (OpDesc.part t d') (Children.part child2 cs2) ++ rest
               = t :: (child2.flatten ++ (Children.flatten d' cs2 ++ rest)) := by
        simp [Children.flatten, List.append_assoc]
      rw [hin]
      simp only [parseChildren, if_true, hpt, Option.map_map, Function.comp_def, RightSublist.trans]
      rw [hr', hpc]
      simp [hr2]
end

/-- Top-level round-trip: every tree's flattening parses (fully) back to it. -/
theorem parseAll_complete {G : Grammar} (t : Tree G) : parseAll (parser G) t.flatten = some t := by
  have h := parseTree_complete t []
  rw [List.append_nil] at h
  obtain ⟨⟨t', r⟩, hpt, heq⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, hr⟩ := heq
  unfold parseAll parser
  rw [hpt]
  simp [hr]

/-- `flatten` is injective — the grammar is unambiguous. -/
theorem flatten_injective {G : Grammar} {t₁ t₂ : Tree G} (h : t₁.flatten = t₂.flatten) : t₁ = t₂ := by
  have h₁ : parseAll (parser G) t₁.flatten = some t₁ := parseAll_complete t₁
  have h₂ : parseAll (parser G) t₂.flatten = some t₂ := parseAll_complete t₂
  rw [h, h₂] at h₁
  injection h₁ with h'
  exact h'.symm

/-- Full characterization: the parser accepts exactly the flattenings, and
returns the unique tree that flattens to the input. -/
theorem parse_iff {G : Grammar} {tkns : List Token} {t : Tree G} :
    parseAll (parser G) tkns = some t ↔ t.flatten = tkns := by
  constructor
  · exact parseAll_sound
  · intro h; subst h; exact parseAll_complete t

end LambdaLab.Parser.Playground
