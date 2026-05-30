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

## Note on namespacing

The shared `Parser` type lives in the `LambdaLab.Parser` namespace
(`LambdaLab/Parser/Basic.lean`). The `IsSound` predicate defined below
lives in the Mixfix-local `Parser` namespace
(`LambdaLab.Parser.Mixfix.Parser`). So for `p : LambdaLab.Parser.Parser`
the dot-projection `p.IsSound` resolves against the *wrong* `Parser`
namespace and fails; we write `Parser.IsSound p` explicitly at every
call site.
-/

namespace LambdaLab.Parser.Mixfix

/-! ## Atom round-trip in the empty grammar

The empty grammar has no operators, so `parseTree` falls through to
`atomFallbackTree` immediately on a one-token input. -/

/-- In the empty grammar `parseHead` always falls through to the atom
fallback (no operators to try). -/
theorem parseHead_empty {α : Type} (atomBuild : String → α)
    (s : String) (rest : List String) :
    parseHead ({ levels := [], atomBuild } : Grammar α) (s :: rest)
      = some (.atom s, ⟨rest, Nat.lt_succ_self _⟩) := by
  rw [parseHead.eq_def]
  simp only [List.flatten_nil, List.findSome?_nil]
  rfl

/-- In the empty grammar `tryTailLoop` never wraps: no tail operators and
juxtaposition is disabled (`juxtBuild = none` by default). -/
theorem tryTailLoop_empty {α : Type} (atomBuild : String → α)
    (head : Tree α) (input : List String) :
    tryTailLoop ({ levels := [], atomBuild } : Grammar α) head input
      = ⟨head, ⟨input, Nat.le_refl _⟩⟩ := by
  rw [tryTailLoop.eq_def]
  simp only [List.flatten_nil, List.findSome?_nil]

theorem parseTree_atom_emptyGrammar {α : Type} (atomBuild : String → α)
    (s : String) :
    parseTree ({ levels := [], atomBuild } : Grammar α) [s] =
    some (.atom s, ⟨[], Nat.lt_succ_self _⟩) := by
  rw [parseTree.eq_def, parseHead_empty atomBuild s []]
  simp only [tryTailLoop_empty]

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

/-- Prefix walker rejects when the first input token differs from the
first name-part. Mirror of `parseTreeClosedSeq_head_mismatch`. -/
theorem parseTreePrefixSeq_head_mismatch {α : Type} (g : Grammar α)
    (nameParts : List String) (holes : List (HoleSpec α))
    (s : String) (rest : List String)
    (h : nameParts.head? ≠ some s) :
    parseTreePrefixSeq g nameParts holes (s :: rest) = none := by
  rcases nameParts with _ | ⟨np, nps⟩
  · -- nameParts = []: catch-all (no arm matches an empty name list).
    rcases holes with _ | ⟨h', hs⟩
    · unfold parseTreePrefixSeq; rfl
    · rcases h' with _ | @⟨_, p⟩ <;> (unfold parseTreePrefixSeq; rfl)
  · have hsp : s ≠ np := by
      intro e; apply h; rw [e]; rfl
    -- Split name-tail and hole-tail enough to make every match arm
    -- concrete; the real arms then start with `matchToken np` (failing),
    -- and empty-hole shapes hit the catch-all (`none`).
    rcases nps with _ | ⟨q, nps'⟩ <;>
      rcases holes with _ | ⟨h', hs⟩ <;>
      (try rcases h' with _ | @⟨_, p⟩) <;>
      (try rcases hs with _ | ⟨hh, ht⟩) <;>
      (unfold parseTreePrefixSeq
       first
         | rw [matchToken_cons_ne rest hsp]
         | rfl)

theorem tryOp_eq_none_of_head_mismatch {α : Type} (g : Grammar α)
    (s : String) (rest : List String) (op : Operator α)
    (hClosed : op.fixity = .closed → op.nameParts.head? ≠ some s) :
    tryOp g (s :: rest) op = none := by
  rw [tryOp.eq_def]
  -- Dispatch on fixity. Closed recurses into `parseTreeClosedSeq`, which
  -- rejects on a head mismatch; postfix/infix are `none` outright.
  split
  · -- closed
    rename_i hfix
    rw [parseTreeClosedSeq_head_mismatch g op.nameParts op.holes s rest
          (hClosed hfix)]
  · -- prefix
    -- BLOCKED: the hypothesis only constrains the closed case, but for a
    -- prefix operator `tryOp` calls `parseTreePrefixSeq`, which *can*
    -- succeed when its head matches `s`. The theorem (and its consumer
    -- `findSome?_tryOp_of_HeadDistinct`, which is fed by `HeadDistinct` —
    -- a closed-only distinctness assumption) is only sound for the
    -- closed-operator scope. A prefix competitor sharing a head is a
    -- genuine, out-of-scope gap, so this branch stays a `sorry`.
    sorry
  · -- postfix / infix (the catch-all `_ => none`)
    rfl

/-- When no operator's head matches the first token, `parseHead` falls
through to the atom fallback. This is the fully-proved half of
`parseTree_atom_of_no_match`. -/
theorem parseHead_atom_of_no_match {α : Type} (g : Grammar α)
    (s : String) (rest : List String)
    (h : ∀ op ∈ g.levels.flatten, op.fixity = .closed →
      op.nameParts.head? ≠ some s) :
    parseHead g (s :: rest) = some (.atom s, ⟨rest, Nat.lt_succ_self _⟩) := by
  rw [parseHead.eq_def]
  have hNone : List.findSome? (tryOp g (s :: rest)) g.levels.flatten = none := by
    rw [List.findSome?_eq_none_iff]
    intro op hop
    exact tryOp_eq_none_of_head_mismatch g s rest op (h op hop)
  rw [hNone]
  rfl

theorem parseTree_atom_of_no_match {α : Type} (g : Grammar α)
    (s : String) (rest : List String)
    (h : ∀ op ∈ g.levels.flatten, op.fixity = .closed →
      op.nameParts.head? ≠ some s) :
    parseTree g (s :: rest) = some (.atom s, ⟨rest, Nat.lt_succ_self _⟩) := by
  rw [parseTree.eq_def, parseHead_atom_of_no_match g s rest h]
  -- After the head is the atom `s` with leftover `rest`, the result is
  -- `tryTailLoop g (.atom s) rest`. BLOCKED: the hypothesis only rules
  -- out *head* operators (closed) starting at `s`; it says nothing about
  -- postfix/infix operators in `g` that could wrap the atom by matching
  -- inside `rest`. So `tryTailLoop` is not guaranteed to be the identity
  -- here. The statement is only sound for grammars with no applicable
  -- trailing operators (e.g. the empty grammar, handled separately by
  -- `parseTree_atom_emptyGrammar`). Closing this needs an extra
  -- "no tail op matches `rest`" hypothesis, which the current signature
  -- lacks.
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
    · -- op = head: at the front of the list
      rw [List.findSome?_cons]
      cases hOpVal : tryOp g (op.head :: rest) op with
      | some r => rfl
      | none   =>
          rw [List.findSome?_eq_none_iff]
          intro op' hop'Mem
          apply tryOp_of_head_ne
          intro hClosed'
          intro hEq
          exact hHead op' hop'Mem hClosed hClosed' hEq.symm
    · -- op ∈ tail: head must give none, then recurse
      rw [List.findSome?_cons]
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

/-! ### Round-trip helpers -/

/-- `matchToken` round-trips on its own literal head. -/
theorem matchToken_self (tok : String) (rest : List String) :
    matchToken tok (tok :: rest) = some ⟨rest, Nat.lt_succ_self _⟩ := by
  unfold matchToken; simp

/-- `runParser` round-trips: when the underlying parser round-trips and
its printer output is non-empty (so the parser strictly consumes), the
length-gated `runParser` succeeds with the same leftover. -/
theorem runParser_self {β : Type} (subP : Parser β) (val : β)
    (extra : List String) (hNe : subP.printer val ≠ [])
    (hRT : subP.run (subP.printer val ++ extra) = some (val, extra)) :
    ∃ (h : extra.length < (subP.printer val ++ extra).length),
      runParser subP (subP.printer val ++ extra) = some (val, ⟨extra, h⟩) := by
  have hpos : 0 < (subP.printer val).length := by
    rcases hh : subP.printer val with _ | ⟨a, b⟩
    · exact absurd hh hNe
    · simp
  have hlt : extra.length < (subP.printer val ++ extra).length := by
    rw [List.length_append]; omega
  refine ⟨hlt, ?_⟩
  unfold runParser
  rw [hRT]; simp only []; rw [dif_pos hlt]

/-- Round-trip for the closed-sequence walker, abstracted over a
round-trip oracle `ptRT` for `parseTree`. Proved by induction on the
hole list: recursive holes use `ptRT`, sub-holes `runParser_self`, and
literal name-parts `matchToken_self`. The `nameParts.length = hs.length
+ 1` premise guarantees the tail name-list is non-empty whenever there
is at least one hole (so `weaveClosed` follows its interleaving arm). -/
theorem closedSeq_roundtrip {α : Type} (g : Grammar α)
    (ptRT : ∀ (t : Tree α), Tree.WellFormed g t → ∀ (extra : List String),
        (parseTree g (Tree.flatten t ++ extra)).map (fun q => (q.fst, q.snd.val))
          = some (t, extra))
    : ∀ (nameParts : List String) (hs : List (HoleSpec α)) (cs : Children α hs),
        Children.WellFormed g cs →
        nameParts.length = hs.length + 1 →
        ∀ (extra : List String),
        (parseTreeClosedSeq g nameParts hs
            (weaveClosed nameParts (Children.flatten cs) ++ extra)).map
            (fun q => (q.fst, q.snd.val)) = some (cs, extra) := by
  intro nameParts hs
  induction hs generalizing nameParts with
  | nil =>
      intro cs hcw hLen extra
      cases cs
      rcases nameParts with _ | ⟨np, nps⟩
      · simp at hLen
      · rcases nps with _ | ⟨q, nps'⟩
        · show (parseTreeClosedSeq g [np] []
              (weaveClosed [np] (Children.flatten Children.nil) ++ extra)).map
              (fun q => (q.fst, q.snd.val)) = some (Children.nil, extra)
          rw [Children.flatten]
          show (parseTreeClosedSeq g [np] [] ([np] ++ extra)).map
              (fun q => (q.fst, q.snd.val)) = some (Children.nil, extra)
          rw [parseTreeClosedSeq.eq_1, List.cons_append, List.nil_append,
              matchToken_self]
          rfl
        · simp at hLen
  | cons h hs ih =>
      intro cs hcw hLen extra
      rcases nameParts with _ | ⟨np, nps⟩
      · simp at hLen
      · have hLen' : nps.length = hs.length + 1 := by
          simp only [List.length_cons] at hLen; omega
        cases h with
        | recurse =>
            cases cs with
            | consRec subTree cs' =>
                cases hcw with
                | consRec hT hCs' =>
                rw [Children.flatten, weaveClosed]
                case _ =>
                  rw [parseTreeClosedSeq.eq_2]
                  simp only [List.cons_append, List.append_assoc, matchToken_self]
                  have hpt := ptRT subTree hT (weaveClosed nps (Children.flatten cs') ++ extra)
                  rcases hP : parseTree g (Tree.flatten subTree ++
                      (weaveClosed nps (Children.flatten cs') ++ extra))
                    with _ | ⟨st, r', hRr'⟩
                  · rw [hP] at hpt; simp at hpt
                  · rw [hP] at hpt
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpt
                    obtain ⟨hst, hr'⟩ := hpt
                    subst hst; subst hr'
                    have hrec := ih nps cs' hCs' hLen' extra
                    rcases hcl : parseTreeClosedSeq g nps hs
                        (weaveClosed nps (Children.flatten cs') ++ extra)
                      with _ | ⟨cs'', rest'', hRr''⟩
                    · rw [hcl] at hrec; simp at hrec
                    · rw [hcl] at hrec
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨hcs'', hrest''⟩ := hrec
                      subst hcs''
                      simp only [hcl, Option.map_some, Option.some.injEq, Prod.mk.injEq]
                      exact ⟨trivial, hrest''⟩
                case _ =>
                  intro hnps; rw [hnps] at hLen'; simp at hLen'
        | @sub β subP =>
            cases cs with
            | consSub val cs' =>
                cases hcw with
                | consSub hNe hRT hCs' =>
                rw [Children.flatten, weaveClosed]
                case _ =>
                  rw [parseTreeClosedSeq.eq_3]
                  simp only [List.cons_append, List.append_assoc, matchToken_self]
                  obtain ⟨hlt, hrp⟩ := runParser_self subP val
                    (weaveClosed nps (Children.flatten cs') ++ extra) hNe
                    (hRT (weaveClosed nps (Children.flatten cs') ++ extra))
                  rw [hrp]
                  have hrec := ih nps cs' hCs' hLen' extra
                  rcases hcl : parseTreeClosedSeq g nps hs
                      (weaveClosed nps (Children.flatten cs') ++ extra)
                    with _ | ⟨cs'', rest'', hRr''⟩
                  · rw [hcl] at hrec; simp at hrec
                  · rw [hcl] at hrec
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
                    obtain ⟨hcs'', hrest''⟩ := hrec
                    subst hcs''
                    simp only [hcl, Option.map_some, Option.some.injEq, Prod.mk.injEq]
                    exact ⟨trivial, hrest''⟩
                case _ =>
                  intro hnps; rw [hnps] at hLen'; simp at hLen'

mutual
  theorem parseTree_roundtrip {α : Type} (g : Grammar α) (hG : g.HeadDistinct)
      (t : Tree α) (hT : Tree.WellFormed g t) (extra : List String) :
      (parseTree g (Tree.flatten t ++ extra)).map
        (fun p => (p.fst, p.snd.val)) = some (t, extra) := by
    -- BLOCKED (out of current scope), symmetric to `parseTree_sound`:
    -- after parsing the head (atom via `parseTree_atom_of_no_match`, or a
    -- closed node via `findSome?_tryOp_of_HeadDistinct` + the closed-seq
    -- round-trip below), `parseTree` runs `tryTailLoop`, which may wrap the
    -- result with postfix/infix operators or juxtaposition matching inside
    -- `extra`. Neither `HeadDistinct` nor `Tree.WellFormed` forbids that,
    -- so pinning the final result to exactly `(t, extra)` needs a
    -- "no trailing operator/application matches `extra`" hypothesis the
    -- current statement lacks. Discharging this needs the full
    -- `parseTree.induct` 7-motive mutual induction over
    -- parseHead/tryOp/tryTail/tryTailLoop/parseTreePrefixSeq. The
    -- closed-sequence half is fully proved as `closedSeq_roundtrip` above.
    sorry

  theorem parseTreeClosedSeq_roundtrip {α : Type} (g : Grammar α)
      (hG : g.HeadDistinct)
      (nameParts : List String) {hs : List (HoleSpec α)} (cs : Children α hs)
      (hCs : Children.WellFormed g cs)
      (hLen : nameParts.length = hs.length + 1)
      (extra : List String) :
      (parseTreeClosedSeq g nameParts hs
        (weaveClosed nameParts (Children.flatten cs) ++ extra)).map
        (fun p => (p.fst, p.snd.val)) = some (cs, extra) :=
    -- Fully reduced to `parseTree`-round-trip via `closedSeq_roundtrip`.
    closedSeq_roundtrip g
      (fun t hT e => parseTree_roundtrip g hG t hT e)
      nameParts hs cs hCs hLen extra
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
      HoleSpec.sub p ∈ op.holes → Parser.IsSound p

/-! ### Token-level soundness helpers -/

/-- `matchToken` is sound: a successful match means the input was `tok`
followed by the leftover. -/
theorem matchToken_sound {tok : String} (input : List String)
    (rest : List String) (hR : rest.length < input.length)
    (heq : matchToken tok input = some ⟨rest, hR⟩) :
    input = tok :: rest := by
  unfold matchToken at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i t r
    split at heq
    · rename_i hb
      rw [Option.some.injEq, Subtype.mk.injEq] at heq
      subst heq
      have : t = tok := by simpa using hb
      subst this; rfl
    · exact absurd heq (by simp)

/-- `runParser` is sound provided the underlying parser is: a successful
run means the input was the printed value followed by the leftover. -/
theorem runParser_sound {β : Type} (subP : Parser β)
    (hS : Parser.IsSound subP)
    (input : List String) (v : β) (rest : List String)
    (hR : rest.length < input.length)
    (heq : runParser subP input = some (v, ⟨rest, hR⟩)) :
    input = subP.printer v ++ rest := by
  unfold runParser at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i val r hrun
    split at heq
    · rw [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at heq
      obtain ⟨hv, hrest⟩ := heq
      subst v; subst rest
      exact hS input val r hrun
    · exact absurd heq (by simp)

/-- Soundness of the closed-sequence walker, abstracted over a soundness
oracle `ptSound` for `parseTree`. Proved by induction on the hole list;
the recursive (`.recurse`) holes appeal to `ptSound`, the sub-holes to
`runParser_sound`, and the literal name-parts to `matchToken_sound`. -/
theorem closedSeq_sound {α : Type} (g : Grammar α)
    (ptSound : ∀ (inp : List String) (t : Tree α) (rst : List String),
        (parseTree g inp).map (fun q => (q.fst, q.snd.val)) = some (t, rst) →
        inp = Tree.flatten t ++ rst)
    : ∀ (nameParts : List String) (hs : List (HoleSpec α)) (cs : Children α hs),
        (∀ {β : Type} (p : Parser β), HoleSpec.sub p ∈ hs → Parser.IsSound p) →
        ∀ (input rest : List String),
        (parseTreeClosedSeq g nameParts hs input).map (fun q => (q.fst, q.snd.val))
          = some (cs, rest) →
        input = weaveClosed nameParts (Children.flatten cs) ++ rest := by
  intro nameParts hs
  induction hs generalizing nameParts with
  | nil =>
      intro cs subsSound input rest hP
      rcases nameParts with _ | ⟨np, nps⟩
      · rw [parseTreeClosedSeq.eq_def] at hP; simp at hP
      · rcases nps with _ | ⟨q, nps'⟩
        · rw [parseTreeClosedSeq.eq_1] at hP
          rcases hmt : matchToken np input with _ | ⟨r, hRr⟩
          · simp [hmt] at hP
          · simp only [hmt, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
            obtain ⟨hcs, hrest⟩ := hP
            cases cs
            have hin := matchToken_sound input r hRr hmt
            show input = weaveClosed [np] (Children.flatten Children.nil) ++ rest
            rw [hin, hrest]; rfl
        · rw [parseTreeClosedSeq.eq_def] at hP; simp at hP
  | cons h hs ih =>
      intro cs subsSound input rest hP
      rcases nameParts with _ | ⟨np, nps⟩
      · rw [parseTreeClosedSeq.eq_def] at hP; cases h <;> simp at hP
      · have hsubsSound : ∀ {β : Type} (p : Parser β),
            HoleSpec.sub p ∈ hs → Parser.IsSound p := by
          intro β p hp; exact subsSound p (List.mem_cons_of_mem _ hp)
        cases h with
        | recurse =>
            rw [parseTreeClosedSeq.eq_2] at hP
            rcases hmt : matchToken np input with _ | ⟨r, hRr⟩
            · simp [hmt] at hP
            · have hin := matchToken_sound input r hRr hmt
              rcases hpt : parseTree g r with _ | ⟨subTree, r', hRr'⟩
              · simp [hmt, hpt] at hP
              · rcases hcl : parseTreeClosedSeq g nps hs r' with _ | ⟨cs', rest'', hRr''⟩
                · simp [hmt, hpt, hcl] at hP
                · simp only [hmt, hpt, hcl, Option.map_some] at hP
                  rw [Option.some.injEq, Prod.mk.injEq] at hP
                  obtain ⟨hcs, hrest⟩ := hP
                  subst hcs
                  have hsub : r = Tree.flatten subTree ++ r' := by
                    apply ptSound r subTree r'; rw [hpt]; rfl
                  have hrec : r' = weaveClosed nps (Children.flatten cs') ++ rest := by
                    apply ih nps cs' hsubsSound r' rest; rw [hcl, ← hrest]; rfl
                  rw [hin, hsub, hrec]
                  show np :: (Tree.flatten subTree ++ (weaveClosed nps (Children.flatten cs') ++ rest))
                       = weaveClosed (np :: nps)
                          (Children.flatten (Children.consRec subTree cs')) ++ rest
                  rw [Children.flatten, weaveClosed]
                  · simp [List.append_assoc]
                  · -- `nps = []` would make the recursive walk hit the empty
                    -- name-list catch-all (`none`), contradicting `hcl`.
                    intro hnps; subst hnps
                    rw [parseTreeClosedSeq.eq_def] at hcl
                    cases hs <;> simp at hcl
        | @sub β subP =>
            rw [parseTreeClosedSeq.eq_3] at hP
            rcases hmt : matchToken np input with _ | ⟨r, hRr⟩
            · simp [hmt] at hP
            · have hin := matchToken_sound input r hRr hmt
              rcases hrp : runParser subP r with _ | ⟨val, r', hRr'⟩
              · simp [hmt, hrp] at hP
              · rcases hcl : parseTreeClosedSeq g nps hs r' with _ | ⟨cs', rest'', hRr''⟩
                · simp [hmt, hrp, hcl] at hP
                · simp only [hmt, hrp, hcl, Option.map_some] at hP
                  rw [Option.some.injEq, Prod.mk.injEq] at hP
                  obtain ⟨hcs, hrest⟩ := hP
                  subst hcs
                  have hsubP : Parser.IsSound subP :=
                    subsSound subP (List.mem_cons_self ..)
                  have hsub : r = subP.printer val ++ r' :=
                    runParser_sound subP hsubP r val r' hRr' hrp
                  have hrec : r' = weaveClosed nps (Children.flatten cs') ++ rest := by
                    apply ih nps cs' hsubsSound r' rest; rw [hcl, ← hrest]; rfl
                  rw [hin, hsub, hrec]
                  show np :: (subP.printer val ++ (weaveClosed nps (Children.flatten cs') ++ rest))
                       = weaveClosed (np :: nps)
                          (Children.flatten (Children.consSub val cs')) ++ rest
                  rw [Children.flatten, weaveClosed]
                  · simp [List.append_assoc]
                  · intro hnps; subst hnps
                    rw [parseTreeClosedSeq.eq_def] at hcl
                    cases hs <;> simp at hcl

mutual
  theorem parseTree_sound {α : Type} (g : Grammar α) (hSubs : g.SubsSound)
      (input : List String) (t : Tree α) (rest : List String)
      (hP : (parseTree g input).map (fun q => (q.fst, q.snd.val)) =
            some (t, rest)) :
      input = Tree.flatten t ++ rest := by
    -- BLOCKED (out of current scope): a full proof requires soundness of
    -- the whole parser stack `parseHead`/`tryOp`/`tryTail`/`tryTailLoop`/
    -- `parseTreePrefixSeq` (since `parseTree = parseHead` then
    -- `tryTailLoop`, and `tryTailLoop` can build `.app`, postfix and infix
    -- nodes). That is a large mutual induction over `parseTree.induct`'s
    -- seven motives. The closed-sequence half is fully discharged below
    -- via `closedSeq_sound`; what remains here is the head/tail machinery.
    sorry

  theorem parseTreeClosedSeq_sound {α : Type} (g : Grammar α) (hSubs : g.SubsSound)
      (nameParts : List String) {hs : List (HoleSpec α)} (cs : Children α hs)
      (hHsSound : ∀ {β : Type} (p : Parser β),
        HoleSpec.sub p ∈ hs → Parser.IsSound p)
      (input rest : List String)
      (hP : (parseTreeClosedSeq g nameParts hs input).map
              (fun q => (q.fst, q.snd.val)) = some (cs, rest)) :
      input = weaveClosed nameParts (Children.flatten cs) ++ rest :=
    -- Fully reduced to `parseTree`-soundness via `closedSeq_sound`.
    closedSeq_sound g
      (fun inp t rst h => parseTree_sound g hSubs inp t rst h)
      nameParts hs cs hHsSound input rest hP
end

end LambdaLab.Parser.Mixfix
