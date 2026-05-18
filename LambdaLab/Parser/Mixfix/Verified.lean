import LambdaLab.Parser.Mixfix.Parser

/-!
# Mixfix parser: round-trip and soundness properties

The aim of this file is the round-trip theorem
`parseTree g (Tree.flatten t) = some (t, [])` for every "well-formed"
parse tree `t`. We build up to it through smaller lemmas.

## Theorem

For a head-distinct grammar `g` and a well-formed parse tree `t`,
`parseTree g (Tree.flatten t ++ extra) = some (t, ⟨extra, _⟩)` (modulo
`Option.map` to drop the subtype proof). Symmetrically, for well-formed
children `cs` and matching `nameParts`, `parseTreeClosedSeq` round-trips.

## Outline

* `Operator.head` — the first name-part. `Grammar.HeadDistinct` —
  pairwise-distinct heads of closed operators.
* `Tree.WellFormed g t` / `Children.WellFormed g cs` — atoms aren't
  operator heads, nodes are closed and present in `g`, sub-children's
  printer/parser pairs round-trip.
* `tryOp_eq_none_of_head_mismatch` and
  `findSome?_tryOp_of_HeadDistinct` — `findSome?` selects the right
  operator under `HeadDistinct`.
* `parseTree_roundtrip` and `parseTreeClosedSeq_roundtrip` — mutual
  induction via `match` on `cs`/`hCs`, dispatching through the
  per-case equation lemmas (`parseTreeClosedSeq.eq_1`/`eq_2`/`eq_3`).
-/

namespace LambdaLab.Parser.Mixfix

/-! ## Atom round-trip in the empty grammar

The empty grammar has no operators, so `parseTree` falls through to
`atomFallbackTree` immediately on a one-token input. -/

-- TODO(refactor): proof relied on `rfl`-by-unfolding behaviour that
-- doesn't survive the SubParser → Parser/Printer split. Re-port.
theorem parseTree_atom_emptyGrammar {α : Type} (atomBuild : String → α)
    (s : String) :
    parseTree ({ levels := [], atomBuild } : Grammar α) [s] =
    some (.atom s, ⟨[], Nat.lt_succ_self _⟩) := by
  sorry

/-! ## A small lemma about `matchToken`

If the first input token differs from `tok`, `matchToken` rejects. -/

theorem matchToken_cons_ne {tok s : String} (rest : List String) (h : s ≠ tok) :
    matchToken tok (s :: rest) = none := by
  show (if (s == tok) = true then _ else none) = none
  have h2 : (s == tok) = false := by
    cases hb : (s == tok) with
    | false => rfl
    | true  =>
        exfalso
        exact h (beq_iff_eq.mp hb)
  rw [h2]
  rfl

/-! ## Closed-sequence head mismatch

If the first name-part of an operator differs from the first input
token, the closed-sequence walker rejects the input. -/

theorem parseTreeClosedSeq_head_mismatch {α : Type} (g : Grammar α)
    (nameParts : List String) (holes : List (HoleSpec α))
    (s : String) (rest : List String)
    (h : nameParts.head? ≠ some s) :
    parseTreeClosedSeq g nameParts holes (s :: rest) = none := by
  rcases nameParts with _ | ⟨np, nps⟩
  · rcases holes with _ | ⟨h', hs⟩
    · show parseTreeClosedSeq g [] [] (s :: rest) = none
      unfold parseTreeClosedSeq; rfl
    · rcases h' with _ | @⟨_, p⟩
      · show parseTreeClosedSeq g [] (.recurse :: hs) (s :: rest) = none
        unfold parseTreeClosedSeq; rfl
      · show parseTreeClosedSeq g [] (.sub p :: hs) (s :: rest) = none
        unfold parseTreeClosedSeq; rfl
  · have hsp : s ≠ np := by
      intro e
      apply h
      show (np :: nps).head? = some s
      rw [e]; rfl
    rcases nps with _ | ⟨q, nps'⟩
    · rcases holes with _ | ⟨h', hs⟩
      · show parseTreeClosedSeq g [np] [] (s :: rest) = none
        unfold parseTreeClosedSeq
        rw [matchToken_cons_ne rest hsp]
      · rcases h' with _ | @⟨_, p⟩
        · show parseTreeClosedSeq g [np] (.recurse :: hs) (s :: rest) = none
          unfold parseTreeClosedSeq
          rw [matchToken_cons_ne rest hsp]
        · show parseTreeClosedSeq g [np] (.sub p :: hs) (s :: rest) = none
          unfold parseTreeClosedSeq
          rw [matchToken_cons_ne rest hsp]
    · rcases holes with _ | ⟨h', hs⟩
      · show parseTreeClosedSeq g (np :: q :: nps') [] (s :: rest) = none
        unfold parseTreeClosedSeq; rfl
      · rcases h' with _ | @⟨_, p⟩
        · show parseTreeClosedSeq g (np :: q :: nps') (.recurse :: hs) (s :: rest) = none
          unfold parseTreeClosedSeq
          rw [matchToken_cons_ne rest hsp]
        · show parseTreeClosedSeq g (np :: q :: nps') (.sub p :: hs) (s :: rest) = none
          unfold parseTreeClosedSeq
          rw [matchToken_cons_ne rest hsp]

/-! ## Atom round-trip with no first-token match

If no closed operator's first name-part equals `s`, every operator
contribution to `findSome?` is `none`, so `parseTree` falls through to
`atomFallbackTree`. -/

-- TODO(refactor): the `rfl` branches after `cases hf` no longer
-- definitionally reduce; needs an explicit `simp [tryOp]` style port.
theorem tryOp_eq_none_of_head_mismatch {α : Type} (g : Grammar α)
    (s : String) (rest : List String) (op : Operator α)
    (hClosed : op.fixity = .closed → op.nameParts.head? ≠ some s) :
    tryOp g (s :: rest) op = none := by
  sorry

-- TODO(refactor): downstream of `parseTree_atom_emptyGrammar` and the
-- `unfold parseTree; rfl` pattern. Re-port once those land.
theorem parseTree_atom_of_no_match {α : Type} (g : Grammar α)
    (s : String) (rest : List String)
    (h : ∀ op ∈ g.levels.flatten, op.fixity = .closed →
      op.nameParts.head? ≠ some s) :
    parseTree g (s :: rest) = some (.atom s, ⟨rest, Nat.lt_succ_self _⟩) := by
  sorry

/-! ## Well-formedness

To state the round-trip theorem cleanly we need two things:

* A **head-distinctness** assumption on the grammar: closed operators
  have pairwise distinct first name-parts. Without this, `findSome?`
  might pick a competitor instead of the operator that produced the
  tree.
* A **well-formedness predicate** on parse trees, requiring atoms not
  to coincide with operator heads, recursive children to be themselves
  well-formed, and sub-children to round-trip through their printer/
  parser pair. -/

/-- The first name-part of an operator. Always well-defined since
`nameParts` is non-empty. -/
def Operator.head {α : Type} (op : Operator α) : String :=
  op.nameParts.head op.nameParts_ne_nil

theorem Operator.nameParts_head?_eq {α : Type} (op : Operator α) :
    op.nameParts.head? = some op.head :=
  List.head?_eq_some_head op.nameParts_ne_nil

/-- Closed operators in `g` have pairwise distinct first name-parts. -/
def Grammar.HeadDistinct {α : Type} (g : Grammar α) : Prop :=
  g.levels.flatten.Pairwise (fun op₁ op₂ =>
    op₁.fixity = .closed → op₂.fixity = .closed → op₁.head ≠ op₂.head)

mutual
  /-- A well-formed parse tree: atoms aren't accidentally heads of any
  closed operator, and node operators are closed and present in `g`. -/
  inductive Tree.WellFormed {α : Type} (g : Grammar α) : Tree α → Prop
    | atom (s : String)
        (h : ∀ op ∈ g.levels.flatten, op.fixity = .closed → op.head ≠ s) :
        Tree.WellFormed g (.atom s)
    | node {op : Operator α} {cs : Children α op.holes}
        (hClosed : op.fixity = .closed)
        (hMem : op ∈ g.levels.flatten)
        (hCs : Children.WellFormed g cs) :
        Tree.WellFormed g (.node op cs)

  /-- A well-formed child list: each recursive child is well-formed, and
  each sub-hole's value round-trips through its printer/parser. -/
  inductive Children.WellFormed {α : Type} (g : Grammar α) :
      ∀ {hs : List (HoleSpec α)}, Children α hs → Prop
    | nil : Children.WellFormed g .nil
    | consRec {hs : List (HoleSpec α)} {t : Tree α} {cs : Children α hs}
        (hT : Tree.WellFormed g t)
        (hCs : Children.WellFormed g cs) :
        Children.WellFormed g (.consRec t cs)
    | consSub {β : Type} {p : Parser β}
              {hs : List (HoleSpec α)}
              {v : β} {cs : Children α hs}
        (hPrintNeNil : p.printer v ≠ [])
        (hRoundTrip : ∀ (extra : List String),
          p.run (p.printer v ++ extra) = some (v, extra))
        (hCs : Children.WellFormed g cs) :
        Children.WellFormed g
          (@Children.consSub α β p hs v cs)
end

/-! ## Op selection under HeadDistinct

If the input is headed by `op.head`, no other closed operator in the
list can match its first name-part (by `HeadDistinct`), and non-closed
operators always fail. So `findSome? (tryOp g input)` returns whatever
`tryOp g input op` returns. -/

/-- Specialised wrapper around `tryOp_eq_none_of_head_mismatch`: if
`op'`'s head differs from `op`'s head, `tryOp` rejects `op.head :: rest`. -/
theorem tryOp_of_head_ne {α : Type} (g : Grammar α)
    (rest : List String) (op op' : Operator α)
    (h : op'.fixity = .closed → op'.head ≠ op.head) :
    tryOp g (op.head :: rest) op' = none := by
  apply tryOp_eq_none_of_head_mismatch
  intro hClosed'
  rw [Operator.nameParts_head?_eq]
  intro hEq
  exact h hClosed' (Option.some.inj hEq)

theorem findSome?_tryOp_of_HeadDistinct {α : Type} (g : Grammar α)
    (rest : List String) (op : Operator α)
    (hClosed : op.fixity = .closed)
    (l : List (Operator α))
    (hP : l.Pairwise (fun op₁ op₂ =>
        op₁.fixity = .closed → op₂.fixity = .closed → op₁.head ≠ op₂.head))
    (hMem : op ∈ l) :
    l.findSome? (tryOp g (op.head :: rest)) =
      tryOp g (op.head :: rest) op := by
  induction l with
  | nil => exact absurd hMem (List.not_mem_nil)
  | cons head tail ih =>
    rw [List.pairwise_cons] at hP
    obtain ⟨hHead, hPtail⟩ := hP
    rw [List.mem_cons] at hMem
    rcases hMem with rfl | hMemTail
    · rw [List.findSome?_cons]
      cases hOpVal : tryOp g (op.head :: rest) op with
      | some r => rfl
      | none   =>
          rw [List.findSome?_eq_none_iff]
          intro op' hop'Mem
          apply tryOp_of_head_ne
          intro hClosed'
          intro hEq
          exact hHead op' hop'Mem hClosed hClosed' hEq.symm
    · rw [List.findSome?_cons]
      have hHeadNone : tryOp g (op.head :: rest) head = none := by
        apply tryOp_of_head_ne
        intro hHeadClosed hEq
        exact hHead op hMemTail hHeadClosed hClosed hEq
      rw [hHeadNone]
      exact ih hPtail hMemTail

/-! ## The round-trip theorem

We strip the subtype proof from parser results using `Option.map`.
That's a presentation choice — the parser still returns subtypes
internally — but removes a class of motive-not-type-correct failures
when rewriting. -/

-- TODO(refactor): proof bodies below were ported from the
-- `SubParser`-era version but the underlying tactics depend on
-- `parseTreeClosedSeq.eq_4` side-condition arities (which changed when
-- `.sub sp` became `.sub β p pr`) and on `unfold; rfl` patterns that
-- no longer reduce in the post-refactor mutual definitions. Theorem
-- statements are kept so the public API remains stable; the bodies
-- need to be re-ported.

mutual
  theorem parseTree_roundtrip {α : Type} (g : Grammar α) (hG : g.HeadDistinct)
      (t : Tree α) (hT : Tree.WellFormed g t)
      (extra : List String) :
      (parseTree g (Tree.flatten t ++ extra)).map
        (fun p => (p.fst, p.snd.val)) = some (t, extra) := by
    sorry

  theorem parseTreeClosedSeq_roundtrip {α : Type} (g : Grammar α)
      (hG : g.HeadDistinct)
      (nameParts : List String) {hs : List (HoleSpec α)} (cs : Children α hs)
      (hCs : Children.WellFormed g cs)
      (hLen : nameParts.length = hs.length + 1)
      (extra : List String) :
      (parseTreeClosedSeq g nameParts hs
        (weaveClosed nameParts (Children.flatten cs) ++ extra)).map
        (fun p => (p.fst, p.snd.val)) = some (cs, extra) := by
    sorry
end

/-! ## Soundness

Soundness is the converse of round-trip: when the parser succeeds, the
returned tree's flatten plus the leftover equals the original input.

In the `.sub` case we need the sub-parser to be a left-inverse of its
printer (otherwise the parser could return a value whose printer's output
isn't a prefix of the consumed tokens). The recursive case has no such
hypothesis — the parser uses `parseTree` itself, whose soundness is the
inductive hypothesis. -/

/-- A `Parser β` is sound if its `run` is a left-inverse of its
`printer`: when `run` accepts, the `printer` reconstructs exactly the
consumed prefix. -/
def Parser.IsSound {β : Type} (p : Parser β) : Prop :=
  ∀ (input : List String) (v : β) (rest : List String),
    p.run input = some (v, rest) → input = p.printer v ++ rest

/-- All sub-parsers used in any operator's holes in `g` are sound. -/
def Grammar.SubsSound {α : Type} (g : Grammar α) : Prop :=
  ∀ op ∈ g.levels.flatten,
    ∀ {β : Type} (p : Parser β),
      HoleSpec.sub p ∈ op.holes → p.IsSound

mutual
  theorem parseTree_sound {α : Type} (g : Grammar α) (hSubs : g.SubsSound)
      (input : List String) (t : Tree α) (rest : List String)
      (hP : (parseTree g input).map
              (fun q => (q.fst, q.snd.val)) =
            some (t, rest)) :
      input = Tree.flatten t ++ rest := by
    sorry

  theorem parseTreeClosedSeq_sound {α : Type} (g : Grammar α)
      (hSubs : g.SubsSound)
      (nameParts : List String) {hs : List (HoleSpec α)}
      (cs : Children α hs)
      (hHsSound : ∀ {β : Type} (p : Parser β),
        HoleSpec.sub p ∈ hs → p.IsSound)
      (input : List String) (rest : List String)
      (hP : (parseTreeClosedSeq g nameParts hs input).map
              (fun q => (q.fst, q.snd.val)) =
            some (cs, rest)) :
      input = weaveClosed nameParts (Children.flatten cs) ++ rest := by
    sorry
end

end LambdaLab.Parser.Mixfix
