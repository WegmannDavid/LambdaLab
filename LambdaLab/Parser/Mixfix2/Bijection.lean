import LambdaLab.Parser.Mixfix2.Tree

/-!
# Flatten / parse bijection (Mixfix2)

`flatten` turns a tree into its token stream; `parse` is intended to be
its inverse. The bijection is the pair of round-trips

* `parse (flatten t) = some t`
* `parse s = some t → flatten t = s`

This file provides `flatten`, `parse` (closed fragment), and the
soundness direction.
-/

namespace LambdaLab.Parser.Mixfix2

/-! ## Weaving name-parts and child token-lists -/

/-- `closed`: `n₀ c₀ n₁ c₁ … nₖ` — name-parts on the outside. -/
def weaveClosed : List String → List (List String) → List String
  | [],          _       => []
  | [p],         _       => [p]
  | p :: _ :: _, []      => [p]
  | p :: ps,     c :: cs => p :: c ++ weaveClosed ps cs

/-- `prefix`: `n₀ c₀ n₁ c₁ … nₖ cₖ` — a child after every name-part. -/
def weavePrefix : List String → List (List String) → List String
  | [],      _       => []
  | _ :: _,  []      => []
  | p :: ps, c :: cs => p :: c ++ weavePrefix ps cs

/-- `postfix`: `c₀ n₀ c₁ n₁ … cₖ nₖ` — a child before every name-part. -/
def weavePostfix : List String → List (List String) → List String
  | [],      _       => []
  | _ :: _,  []      => []
  | p :: ps, c :: cs => c ++ p :: weavePostfix ps cs

/-- `infix`: `c₀ n₀ c₁ n₁ … nₖ cₖ₊₁` — children on the outside. -/
def weaveInfix : List String → List (List String) → List String
  | [],      []       => []
  | [],      [c]      => c
  | [],      _ :: _   => []
  | _ :: _,  []       => []
  | p :: ps, c :: cs  => c ++ p :: weaveInfix ps cs

/-! ## Flatten -/

mutual
  /-- Token stream of a tree. `top` flattens its node; `next` is a pure
  weakening and flattens its subtree unchanged. -/
  def Tree.flatten {G d} : Tree G d → List String
    | .top n  => n.flatten
    | .next t => t.flatten

  /-- Token stream of a node: weave the operator's name-parts with the
  flattened children, dispatched on fixity. -/
  def Node.flatten {G d} : Node G d → List String
    | .mk h cs =>
        let parts := cs.flatten
        let Op := G.ops[d]'h
        match Op.fixity with
        | .closed  => weaveClosed  Op.nameParts parts
        | .prefix  => weavePrefix  Op.nameParts parts
        | .postfix => weavePostfix Op.nameParts parts
        | .infix _ => weaveInfix   Op.nameParts parts

  /-- Flattened children, in token order. -/
  def Children.flatten {G Ls} : Children G Ls → List (List String)
    | .nil       => []
    | .cons t cs => t.flatten :: cs.flatten
end

/-! ## Parsing (closed fragment)

`parse` is recursive-descent over precedence levels (depths into `G`).
It is restricted, for now, to operators that begin with a name-part —
`closed` operators (and the nullary `closed` constants); other fixities
are skipped via `next`.

Termination is well-founded on `(s.length, G.length - d)` lexicographically.
`parse` returns a *sized* suffix `Rest s` (`{ r // r.length ≤ s.length }`)
so each recursive call carries the bound the measure needs. -/

/-- Build the homogeneous interior children of a closed operator (all at
the loosest level `0`) from a plain list of trees. -/
def listToChildren {G : Grammar} :
    (cs : List (Tree G 0)) → Children G (List.replicate cs.length 0)
  | []      => .nil
  | c :: cs => .cons c (listToChildren cs)

theorem childLevels_closed (Op : Operator) (d : Nat) (h : Op.fixity = .closed) :
    Op.childLevels d = List.replicate (Op.nameParts.length - 1) 0 := by
  simp [Operator.childLevels, h]

/-- The index equality witnessing that a length-matched list of trees has
exactly a closed operator's child-levels. -/
theorem childLevels_closed_replicate (Op : Operator) (d : Nat)
    (h : Op.fixity = .closed) (cs : List (Tree G 0))
    (hlen : cs.length = Op.nameParts.length - 1) :
    Op.childLevels d = List.replicate cs.length 0 := by
  rw [childLevels_closed Op d h, hlen]

/-- Smart constructor for a closed node from its interior children given
as a length-matched list. The operator at depth `d` is `G.ops[d]`. -/
def Node.mkClosed {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hc : (G.ops[d]'h).fixity = .closed) (cs : List (Tree G 0))
    (hlen : cs.length = (G.ops[d]'h).nameParts.length - 1) : Node G d :=
  .mk h ((childLevels_closed_replicate (G.ops[d]'h) d hc cs hlen).symm ▸ listToChildren cs)

/-- The unconsumed suffix returned by a parser: a token list provably no
longer than the input. -/
abbrev Rest (s : List String) : Type := { r : List String // r.length ≤ s.length }

section
variable (G : Grammar)

mutual
  /-- Parse a tree at level `d` from `s`, returning it with the
  unconsumed suffix. -/
  def parse : (d : Nat) → (s : List String) → Option (Tree G d × Rest s)
    | d, s =>
        if h : d < G.ops.size then
          match hf : (G.ops[d]'h).fixity with
          | .closed =>
              match parseClosedBody (G.ops[d]'h).nameParts s with
              | some (cs, r) =>
                  if hlen : cs.length = (G.ops[d]'h).nameParts.length - 1 then
                    some (.top (Node.mkClosed h hf cs hlen), r)
                  else
                    match parse (d + 1) s with
                    | some (t, r) => some (.next t, r)
                    | none        => none
              | none =>
                  match parse (d + 1) s with
                  | some (t, r) => some (.next t, r)
                  | none        => none
          | _ =>
              match parse (d + 1) s with
              | some (t, r) => some (.next t, r)
              | none        => none
        else none
  termination_by d s => (s.length, G.ops.size - d)
  decreasing_by
    all_goals
      simp_wf
      apply Prod.Lex.right
      omega

  /-- Parse the body of a closed operator: name-parts on the outside,
  interior children (each at level `0`) in between. -/
  def parseClosedBody : (names : List String) → (s : List String) →
      Option (List (Tree G 0) × Rest s)
    | [],            _ => none
    | [_n],          s =>
        match s with
        | t :: r => if t = _n then some ([], ⟨r, by simp⟩) else none
        | []     => none
    | n :: n' :: ns, s =>
        match s with
        | t :: r₀ =>
            if t = n then
              match parse 0 r₀ with
              | some (c, ⟨r₁, h₁⟩) =>
                  match parseClosedBody (n' :: ns) r₁ with
                  | some (cs, ⟨r₂, h₂⟩) =>
                      some (c :: cs, ⟨r₂, by simp only [List.length_cons]; omega⟩)
                  | none => none
              | none => none
            else none
        | [] => none
  termination_by _names s => (s.length, 0)
  decreasing_by
    all_goals
      simp_wf
      apply Prod.Lex.left
      omega
end

end

/-! ## Soundness: whatever `parse` returns flattens back

`parse d s = some (t, r)` implies `t.flatten ++ r.val = s`. No grammar
hypotheses are needed — this direction is pure bookkeeping. -/

@[simp] theorem listToChildren_flatten {G : Grammar} (cs : List (Tree G 0)) :
    (listToChildren cs).flatten = cs.map (·.flatten) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [listToChildren, Children.flatten, ih]

theorem Children.flatten_cast {G : Grammar} {Ls₁ Ls₂ : List Nat}
    (h : Ls₁ = Ls₂) (x : Children G Ls₁) : (h ▸ x).flatten = x.flatten := by
  cases h; rfl

theorem Node.mkClosed_flatten {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hc : (G.ops[d]'h).fixity = .closed) (cs : List (Tree G 0))
    (hlen : cs.length = (G.ops[d]'h).nameParts.length - 1) :
    (Node.mkClosed h hc cs hlen).flatten
      = weaveClosed (G.ops[d]'h).nameParts (cs.map (·.flatten)) := by
  unfold Node.mkClosed Node.flatten
  simp only [hc]
  rw [Children.flatten_cast, listToChildren_flatten]

/-- Parse soundness, as a motive over `parse`. -/
def Sound1 (G : Grammar) (d : Nat) (s : List String) : Prop :=
  ∀ (t : Tree G d) (r : Rest s), parse G d s = some (t, r) → t.flatten ++ r.val = s

/-- Closed-body soundness, as a motive over `parseClosedBody`. -/
def Sound2 (G : Grammar) (names s : List String) : Prop :=
  ∀ (cs : List (Tree G 0)) (r : Rest s), parseClosedBody G names s = some (cs, r) →
    weaveClosed names (cs.map (·.flatten)) ++ r.val = s ∧ cs.length = names.length - 1

set_option linter.unusedSimpArgs false in
theorem parse_sound (G : Grammar) :
    (∀ (d : Nat) s t (r : Rest s),
        parse G d s = some (t, r) → t.flatten ++ r.val = s) ∧
    (∀ names s cs (r : Rest s),
        parseClosedBody G names s = some (cs, r) →
          weaveClosed names (cs.map (·.flatten)) ++ r.val = s
            ∧ cs.length = names.length - 1) := by
  -- the `next` (level-descent) path: when `parse (d+1) s` succeeds.
  have hns : ∀ (d : Nat) (s : List String) (t : Tree G (d + 1)) (r : Rest s)
      (t' : Tree G d) (r' : Rest s),
      parse G (d + 1) s = some (t, r) →
      (match parse G (d + 1) s with
        | some (t, r) => some (Tree.next t, r) | none => none) = some (t', r') →
      Sound1 G (d + 1) s → t'.flatten ++ r'.val = s := by
    intro d s t r t' r' hpar heq ih
    rw [hpar] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simpa [Tree.flatten] using ih t r hpar
  refine ⟨parse.induct G (Sound1 G) (Sound2 G)
            ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17,
          parseClosedBody.induct G (Sound1 G) (Sound2 G)
            ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17⟩
  -- c1: closed, body some, length ok → `top`
  case c1 =>
    intro d s h hfc cs r hb hlen ih2 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (simp only [hb, dif_pos hlen, Option.some.injEq, Prod.mk.injEq] at heq
         obtain ⟨rfl, rfl⟩ := heq
         obtain ⟨hbody, _⟩ := ih2 cs r hb
         simpa [Tree.flatten, Node.mkClosed_flatten] using hbody)
      | simp_all
  -- c2: closed, body some, length wrong, parse(d+1) some → next
  case c2 =>
    intro d s h hfc cs r hb hnlen t₀ r₀ hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (simp only [hb, dif_neg hnlen] at heq; exact hns _ _ _ _ _ _ hpar heq ih1)
      | exact hns _ _ _ _ _ _ hpar heq ih1
  -- c3: closed, body some, length wrong, parse(d+1) none → fails
  case c3 =>
    intro d s h hfc cs r hb hnlen hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (simp only [hb, dif_neg hnlen] at heq; rw [hpar] at heq; simp at heq)
      | (rw [hpar] at heq; simp at heq)
  -- c4: closed, body none, parse(d+1) some → next
  case c4 =>
    intro d s h hfc hb t₀ r₀ hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (simp only [hb] at heq; exact hns _ _ _ _ _ _ hpar heq ih1)
      | exact hns _ _ _ _ _ _ hpar heq ih1
  -- c5: closed, body none, parse(d+1) none → fails
  case c5 =>
    intro d s h hfc hb hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (simp only [hb] at heq; rw [hpar] at heq; simp at heq)
      | (rw [hpar] at heq; simp at heq)
  -- c6: not closed, parse(d+1) some → next
  case c6 =>
    intro d s h t₀ r₀ hpar hnc ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | exact hns _ _ _ _ _ _ hpar heq ih1
      | exact absurd ‹_› hnc
  -- c7: not closed, parse(d+1) none → fails
  case c7 =>
    intro d s h hpar hnc ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | exact absurd ‹_› hnc
      | (rw [hpar] at heq; simp at heq)
  -- c8: out of bounds → `parse` is `none`
  case c8 =>
    intro d s hoob t' r' heq
    unfold parse at heq; rw [dif_neg hoob] at heq; simp at heq
  -- c9–c17: parseClosedBody
  case c9 => intro s cs r heq; unfold parseClosedBody at heq; simp at heq
  case c10 =>
    intro t r cs r' heq
    unfold parseClosedBody at heq
    simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨by simp [weaveClosed], rfl⟩
  case c11 => intro _n t r hnt cs r' heq; unfold parseClosedBody at heq; simp [if_neg hnt] at heq
  case c12 => intro _n cs r heq; unfold parseClosedBody at heq; simp at heq
  case c13 =>
    intro n' ns t r c r₁ h₁ hpc cs r₂ h₂ hpb ih1 ih2 cs' r' heq
    unfold parseClosedBody at heq
    simp only [if_pos rfl, hpc, hpb, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hc := ih1 c ⟨r₁, h₁⟩ hpc
    obtain ⟨hbody, hlen'⟩ := ih2 cs ⟨r₂, h₂⟩ hpb
    refine ⟨?_, by simp only [List.length_cons] at hlen' ⊢; omega⟩
    simp only [List.map_cons, weaveClosed, List.cons_append, List.append_assoc]
    rw [hbody, hc]
  case c14 =>
    intro n' ns t r c r₁ h₁ hpc hpb _ih1 _ih2 cs' r' heq
    unfold parseClosedBody at heq; simp [if_pos rfl, hpc, hpb] at heq
  case c15 =>
    intro n' ns t r hpc _ih1 cs' r' heq
    unfold parseClosedBody at heq; simp [if_pos rfl, hpc] at heq
  case c16 =>
    intro n n' ns t r hnt cs' r' heq; unfold parseClosedBody at heq; simp [if_neg hnt] at heq
  case c17 =>
    intro n n' ns cs' r' heq; unfold parseClosedBody at heq; simp at heq
