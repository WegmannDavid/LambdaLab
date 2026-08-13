import LambdaLab.Parser.IsoParser.Mixfix.Complete

/-!
# Unambiguity is a THEOREM, not a hypothesis

`Complete.lean` takes `Unambiguous G` (`flatten` injective) as a hypothesis, and it must: for
*any* deterministic parser, two distinct trees that flatten alike make completeness-as-equality
false. The question this file answers is whether a grammar has to *assert* it.

It does not. The three lexical conditions already forced on a grammar —

* `headsDistinct`      — an operator's *leading* token identifies it,
* `varDisjoint`        — no name token is a variable,
* `interiorTerminates` — a token after an interior seam heads no operator of the hole's entry,

— together with the fact that hole levels are fixed by the **fixity** rather than by the grammar
author (`Operator.body`), appear to imply unambiguity outright. `unambiguity-hunt.py` (beside this
file) models `Tree.lean` exactly and finds **no** ambiguous grammar among ~39k exhaustively
enumerated and ~26k random ones; with `interiorTerminates` switched off it finds one within the
first 139. That is the evidence. This file is the proof.

## The shape of the argument

Not "flatten is injective" directly — that statement is too weak to induct on. The load-bearing
statement is **prefix-form unique decomposition**: two trees at the same level whose flattenings
*agree up to a leftover*, where both leftovers **stop** the level, are equal *and* their leftovers
are equal. Unambiguity is then the `rest = []` instance, and `[]` stops every level vacuously.

This is the standard route (Danielsson–Norell §4) and the earlier stack got a long way with it in
`ParserOld/Mixfix/Unambiguity.lean`. Two things do not port:

* that development assumed `NonAssoc` — **no juxtaposition and no associative infix**. Those are
  exactly the fixities we now have, and exactly the ones where a naive `Stops` induction breaks
  (see `stopsLeft` below);
* it keyed on `UniqueNameParts` (a token-counting certificate) rather than on the three conditions
  above, which are strictly more permissive (they allow the same interior token in two different
  operators, e.g. `A _ C` and `B _ C`).
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

variable {Tok : Type} {G : Grammar Tok}

/-! ## A printed tree is never empty

Needed everywhere: the leftover after parsing `t.flatten ++ rest` must be a *strict* suffix, so
`t.flatten` has to be non-empty. It is, and the reason is structural — a variable prints one
token, and every operator body contains either a name part or a hole (which prints non-empty by
induction). -/

/-- A notation always has at least one name token. -/
theorem Notation.toParts_ne_nil (n : Notation Tok G.Ent) :
    Notation.toParts n ≠ [] := by
  cases n <;> simp [Notation.toParts]

/-- Every operator body has at least one part — a name token, or a hole. -/
theorem Operator.body_ne_nil {e : G.Ent} (o : (G.entry e).Op) :
    Operator.body e o ≠ [] := by
  unfold Operator.body
  cases (G.entry e).operator o <;>
    simp [Notation.toParts_ne_nil]

mutual
  theorem Expr.flatten_ne_nil {e : G.Ent} {l : Level (G.entry e)} :
      ∀ (t : Expr G e l), t.flatten ≠ []
    | .var _ _ => by simp [Expr.flatten]
    | .op o _ ps => by
        simp only [Expr.flatten]
        exact Parts.flatten_ne_nil ps (Operator.body_ne_nil o)

  theorem Parts.flatten_ne_nil {shape : List (Part G)} :
      ∀ (ps : Parts G shape), shape ≠ [] → ps.flatten ≠ []
    | .nil, h => absurd rfl h
    | .namePart _ _, _ => by simp [Parts.flatten]
    | .hole ex _, _ => by
        simp only [Parts.flatten]
        intro hcon
        exact Expr.flatten_ne_nil ex (List.append_eq_nil_iff.mp hcon).1
end

/-! ## Sizes, for the mutual termination

`Expr.size`/`Parts.size` (`Tree.lean`) and `Parts.size_cast` (`Complete.lean`) are already in the
tree — this file's ancestor carried its own copies, which the port drops. -/

/-! ## The shape of an operator body, and the first token of a tree

An operator body starts either with the operator's own **head token** (`closed`, `prefx`) or with a
**hole at the host entry** (the left operand of `infx`/`infxl`/`infxr`/`postfx`/`juxt`). The second
half matters: the leading hole is at `e` itself, never at some other entry, so the recursion below
stays inside one entry. -/

theorem Notation.toParts_cons (n : Notation Tok G.Ent) :
    Notation.toParts (G := G) n = .namePart n.firstTok :: (Notation.toParts (G := G) n).tail := by
  cases n <;> rfl

theorem Notation.head?_toTokens {Ent : Type} (n : Notation Tok Ent) :
    n.toTokens.head? = some n.firstTok := by
  cases n <;> rfl

theorem Notation.toParts_append_cons (n : Notation Tok G.Ent) (suffix : List (Part G)) :
    Notation.toParts (G := G) n ++ suffix
      = .namePart n.firstTok :: ((Notation.toParts (G := G) n).tail ++ suffix) := by
  cases n <;> rfl

/-- A **token-led** operator's body begins with its head token. -/
theorem body_cons_namePart {e : G.Ent} (o : (G.entry e).Op)
    (h : ((G.entry e).operator o).startsWithHole = false) :
    ∃ tk ps, Operator.body e o = .namePart tk :: ps ∧
      ((G.entry e).operator o).headTok? = some tk := by
  unfold Operator.body
  cases hop : (G.entry e).operator o with
  | closed n =>
      exact ⟨n.firstTok, (Notation.toParts (G := G) n).tail, Notation.toParts_cons n,
        by simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]⟩
  | prefx n =>
      exact ⟨n.firstTok, (Notation.toParts (G := G) n).tail ++ [.hole e (.tighter o)],
        Notation.toParts_append_cons n _,
        by simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]⟩
  | infx n   => rw [hop] at h; simp [Operator.startsWithHole] at h
  | infxl n  => rw [hop] at h; simp [Operator.startsWithHole] at h
  | infxr n  => rw [hop] at h; simp [Operator.startsWithHole] at h
  | postfx n => rw [hop] at h; simp [Operator.startsWithHole] at h
  | juxt     => rw [hop] at h; simp [Operator.startsWithHole] at h

/-- A **hole-led** operator's body begins with a hole **at the host entry**. -/
theorem body_cons_hole {e : G.Ent} (o : (G.entry e).Op)
    (h : ((G.entry e).operator o).startsWithHole = true) :
    ∃ (L : Level (G.entry e)) (ps : List (Part G)), Operator.body e o = .hole e L :: ps := by
  unfold Operator.body
  cases hop : (G.entry e).operator o with
  | closed n => rw [hop] at h; simp [Operator.startsWithHole] at h
  | prefx n  => rw [hop] at h; simp [Operator.startsWithHole] at h
  | infx n   => exact ⟨.tighter o, _, rfl⟩
  | infxl n  => exact ⟨.tighterEq o, _, rfl⟩
  | infxr n  => exact ⟨.tighter o, _, rfl⟩
  | postfx n => exact ⟨.tighter o, _, rfl⟩
  | juxt     => exact ⟨.tighterEq o, _, rfl⟩

theorem Parts.flatten_cons_namePart {tk : Tok} {ps : List (Part G)}
    (q : Parts G (.namePart tk :: ps)) : ∃ r, q.flatten = tk :: r := by
  cases q with | namePart _ rest => exact ⟨rest.flatten, rfl⟩

theorem Parts.flatten_cons_hole {e' : G.Ent} {L : Level (G.entry e')} {ps : List (Part G)}
    (q : Parts G (.hole e' L :: ps)) :
    ∃ (sub : Expr G e' L) (r : List (Tok)),
      q.flatten = sub.flatten ++ r ∧ sub.size < q.size := by
  cases q with
  | hole sub rest => exact ⟨sub, rest.flatten, rfl, by simp [Parts.size]; omega⟩

/-! From here on the statements mention `startsOperand`/`ContinuesAt`/`FollowAt`, which decide
token equality, so `DecidableEq Tok` enters. Everything above is pure shape reasoning and does not
need it — hence the split, rather than one `omit` per theorem. -/

variable [DecidableEq Tok]

/-- **The first token of any tree starts an operand.** A variable does by definition; a token-led
operator does because its head is the head of a non-hole-led operator; a hole-led one inherits it
from its left operand, which lives at the *same entry*. -/
theorem Expr.flatten_head {e : G.Ent} {l : Level (G.entry e)} (t : Expr G e l) :
    ∃ tk r, t.flatten = tk :: r ∧ startsOperand e tk := by
  match t with
  | .var tk hv => exact ⟨tk, [], rfl, by simp [startsOperand, hv]⟩
  | .op o hc ps =>
      by_cases hh : ((G.entry e).operator o).startsWithHole = true
      · -- hole-led: recurse into the left operand (same entry, strictly smaller)
        obtain ⟨L, ps', hshape⟩ := body_cons_hole o hh
        obtain ⟨sub, r, hfl, hsz⟩ := Parts.flatten_cons_hole (hshape ▸ ps)
        have hsz' : sub.size < (Expr.op o hc ps).size := by
          rw [Expr.size, ← Parts.size_cast hshape ps]; omega
        obtain ⟨tk, r', h1, h2⟩ := Expr.flatten_head sub
        refine ⟨tk, r' ++ r, ?_, h2⟩
        rw [Expr.flatten, ← Parts.flatten_cast hshape ps, hfl, h1, List.cons_append]
      · -- token-led: the head token itself
        rw [Bool.not_eq_true] at hh
        obtain ⟨tk, ps', hshape, hhead⟩ := body_cons_namePart o hh
        obtain ⟨r, hfl⟩ := Parts.flatten_cons_namePart (hshape ▸ ps)
        refine ⟨tk, r, by rw [Expr.flatten, ← Parts.flatten_cast hshape ps, hfl], ?_⟩
        simp only [startsOperand, Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨o, (G.entry e).ops_complete o, by simp [hh, hhead]⟩
  termination_by t.size

/-! ## `Stops` — the per-level FOLLOW, as the induction consumes it

`FollowAt` (in `Biparser.lean`) is already the right predicate. What the induction needs on top of
it is that stopping a **looser** level stops every **tighter** one: an operand sitting at a tighter
level is stopped by anything that stops the ambient level, because fewer operators are applicable
down there. That is `Stops.tighten` below, and it rests on the up-closure of `Level.condition`. -/

/-- Reachability is transitive, so an operator valid at `l` makes everything *tighter* than it
valid at `l` too. -/
theorem TighterEq.trans {Op : Type} {t : Op → List Op} {a b c : Op}
    (h₁ : TighterEq t a b) (h₂ : TighterEq t b c) : TighterEq t a c := by
  induction h₁ with
  | refl => exact h₂
  | step hm _ ih => exact .step hm (ih h₂)

theorem Tighter.toTighterEq' {Op : Type} {t : Op → List Op} {a b : Op}
    (h : Tighter t a b) : TighterEq t a b := by
  induction h with
  | base hm => exact .step hm .refl
  | step hm _ ih => exact .step hm ih

/-- Extend a strictly-tighter path by one more step at the far end. -/
theorem Tighter.snoc {Op : Type} {t : Op → List Op} {a o b : Op}
    (h : Tighter t a o) (hm : b ∈ t o) : Tighter t a b := by
  induction h with
  | base hb => exact .step hb (.base hm)
  | step hb _ ih => exact .step hb (ih hm)

omit [DecidableEq Tok] in
/-- **Up-closure of the level condition.** If `o` inhabits level `l` and `o'` is at least as tight
as `o`, then `o'` inhabits `l` as well. -/
theorem Level.condition_up {e : G.Ent} {l : Level (G.entry e)} {o o' : (G.entry e).Op}
    (hc : Level.condition l o) (ht : TighterEq (G.entry e).tighter o o') :
    Level.condition l o' := by
  cases l with
  | tighter a =>
      -- `Tighter a o` then `TighterEq o o'` gives `Tighter a o'`
      revert hc
      induction ht with
      | refl => exact id
      | step hm _ ih => exact fun hc => ih (hc.snoc hm)
  | tighterEq a => exact TighterEq.trans hc ht
  | loosest =>
      obtain ⟨a, ha, hr⟩ := hc
      exact ⟨a, ha, TighterEq.trans hr ht⟩

/-- **Stopping a looser level stops a tighter one.** An operand of `o` sits at `.tighter o` or
`.tighterEq o`; anything that stops the ambient level `l` (at which `o` itself is applicable) also
stops those, because every operator applicable down there is applicable at `l`. -/
theorem FollowAt.tighten {e : G.Ent} {l l' : Level (G.entry e)}
    (hup : ∀ o, Level.condition l' o → Level.condition l o)
    {rest : List (Tok)} (h : FollowAt e l rest) : FollowAt e l' rest := by
  intro t ht hcon
  refine h t ht ?_
  rcases hcon with ⟨o, hc, hhole, hhead⟩ | ⟨j, hc, hj, hs⟩
  · exact .inl ⟨o, hup o hc, hhole, hhead⟩
  · exact .inr ⟨j, hup j hc, hj, hs⟩

omit [DecidableEq Tok] in
/-- The two instances the body of an operator actually needs. -/
theorem condition_tighter_up {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) :
    ∀ o', Level.condition (.tighter o) o' → Level.condition l o' :=
  fun _ h => Level.condition_up hc (Tighter.toTighterEq' h)

omit [DecidableEq Tok] in
theorem condition_tighterEq_up {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) :
    ∀ o', Level.condition (.tighterEq o) o' → Level.condition l o' :=
  fun _ h => Level.condition_up hc h


/-! ## Facts every version of the argument needs

These are independent of how the left-recursive kernel is finally closed, and they are where the
three grammar conditions actually get *used*. -/

/-! `Tighter.irrefl` is `Complete.lean`'s. It is stated there as `Tighter … o o → False` via the
explicit `rank`, rather than the well-founded-descent form this file's ancestor used; call sites
below take the hypothesis directly instead of the operator. -/

/-- A strictly-tighter path composed with a tighter-or-equal one stays strict. -/
theorem Tighter.trans_tighterEq {Op : Type} {t : Op → List Op} {a b c : Op}
    (h₁ : Tighter t a b) (h₂ : TighterEq t b c) : Tighter t a c := by
  induction h₂ with
  | refl => exact h₁
  | step hm _ ih => exact ih (h₁.snoc hm)

/-! ### The interior tokens of a notation are exactly its seam tokens

`interiorTerminates` is phrased over `holeFollowers` (entry-tagged seams) because that is what the
*law* needs. The unambiguity argument wants the same fact phrased over `nameTokens.tail`. They are
the same list of tokens, and this is the bridge. -/

omit [DecidableEq Tok] in
/-- A notation's token list is its first token followed by its interior tokens. -/
theorem Notation.toTokens_eq {Ent : Type} (n : Notation Tok Ent) :
    n.toTokens = n.firstTok :: n.toTokens.tail := by
  cases n <;> simp [Notation.toTokens, Notation.firstTok]

omit [DecidableEq Tok] in
theorem Notation.mem_tail_toTokens {Ent : Type} (n : Notation Tok Ent)
    {t : Tok} (h : t ∈ n.toTokens.tail) : ∃ e', (e', t) ∈ n.holeFollowers := by
  induction n with
  | last a => simp [Notation.toTokens] at h
  | cons a e' rest ih =>
      simp only [Notation.toTokens, List.tail_cons] at h
      rw [Notation.toTokens_eq rest, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨e', by simp [Notation.holeFollowers]⟩
      · obtain ⟨e₀, h₀⟩ := ih h
        exact ⟨e₀, by simp [Notation.holeFollowers, h₀]⟩

omit [DecidableEq Tok] in
theorem Operator.mem_tail_nameTokens {Ent : Type} (o : Operator Tok Ent)
    {t : Tok} (h : t ∈ o.nameTokens.tail) : ∃ e', (e', t) ∈ o.holeFollowers := by
  cases o with
  | closed n => exact Notation.mem_tail_toTokens n h
  | prefx n  => exact Notation.mem_tail_toTokens n h
  | infx n   => exact Notation.mem_tail_toTokens n h
  | infxl n  => exact Notation.mem_tail_toTokens n h
  | infxr n  => exact Notation.mem_tail_toTokens n h
  | postfx n => exact Notation.mem_tail_toTokens n h
  | juxt     => simp [Operator.nameTokens] at h

/-! ### ⚠ A cross-entry subtlety — do NOT "fix" this by strengthening the grammar

The obvious next lemma is *"a leading token is never an interior token"*: if `t` heads an operator
then seeing `t` after a seam is impossible, so a body token that heads something must *be* a head.

**That lemma is not available, and it should not be made available.** `Grammar.interiorTerminates`
constrains a seam token `t` with respect to the **hole's** entry `e'` — `t` is neither an
`e'`-variable nor the head of any `e'`-operator. It says nothing about the **host** entry `e`. When
the hole is cross-entry (`e' ≠ e`), `t` may perfectly well head an operator of `e`.

The temptation is to strengthen the field to cover the host entry too. `unambiguity-hunt2.py`
(beside this file) says **don't**: over 5370 well-formed *two-entry* grammars it finds no ambiguity
under the condition as shipped, and strengthening it to constrain the host entry as well rules out
grammars without ruling out any ambiguity. The condition is not too weak — this formulation of the
lemma is simply the wrong shape, and the argument has to phrase its appeals to `interiorTerminates`
at **the hole's entry**, which is where the sub-tree comparison actually happens. -/

/-! ## ⚠ Where the left-recursive fixities bite

For a `closed`/`prefx`/`infx`/`postfx` operator every hole's continuation begins with either a
name token of the operator (an interior seam — stopped by `follow_of_holeFollower`) or the ambient
leftover (stopped by `Stops.tighten`). The induction walks the body front-to-back and every operand
is bounded. That is the `NonAssoc` fragment the earlier stack proved.

`infxl`, `infxr` and `juxt` are different, and the difference is not incidental — it *is*
associativity. The left operand of an `infxl o` sits at `.tighterEq o`, and its continuation begins
with **`o`'s own leading token**. But `o` is applicable at `.tighterEq o` (by reflexivity), so that
token **continues** the level by definition: `FollowAt e (.tighterEq o) (headTok o :: _)` is
*false*. There is no FOLLOW-based bound on the left operand, and there cannot be — `a + b + c`
means `(a + b) + c` precisely because the left operand is allowed to run through a `+`.

So these operators need a different bound: the left operand is the **longest** decomposition, and
uniqueness comes from the right operand sitting at `.tighter o` — *strictly* tighter — so it can
carry no `o` at its top. Formally that is a depth-0/bracket-counting argument on the flattening,
which is the kernel Danielsson–Norell only sketch and the earlier stack also left open
(`topOp_unique_holeLed`). It is isolated as `splitLeftRec` below and is the whole remaining task.

`juxt` is the sharpest case: it has **no token at all**, so the split of `f x y` into
`juxt (juxt f x) y` is bounded by nothing lexical whatsoever — only by the right operand being a
single tightest operand. -/


/-! ## ★ The crux: FOLLOW *is* available one level down

The apparent dead-end was this: an `infxl o`'s left operand sits at `.tighterEq o`, and its
continuation begins with `o`'s own head token, which **continues** that level. True — but it is the
wrong level to look at.

Split on the left operand's top operator:

* if it is **strictly tighter** than `o`, the operand is a tree at `.tighter o` — and `headTok o`
  does **not** continue *there*. By `headsDistinct` the only operator that token heads is `o`
  itself, and by `Tighter.irrefl` `o` is not strictly tighter than `o`. So FOLLOW is available
  after all, one level down;
* if it is `o` itself, we recurse into a structurally **smaller** left spine.

That is the whole induction. `juxt` works the same way, with `startsOperand` in place of a head
token: juxtaposition continues via an *operand*, and juxtaposition is not applicable at
`.tighter j` — again by irreflexivity. -/

omit [DecidableEq Tok] in
/-- A leading token is one of the operator's name tokens. -/
theorem Operator.headTok?_mem {Ent : Type} (o : Operator Tok Ent)
    {t : Tok} (h : o.headTok? = some t) : t ∈ o.nameTokens := by
  have h' : o.nameTokens.head? = some t := h
  cases hn : o.nameTokens with
  | nil => rw [hn] at h'; simp at h'
  | cons a rest =>
      rw [hn] at h'
      simp only [List.head?_cons, Option.some.injEq] at h'
      subst h'
      simp

omit [DecidableEq Tok] in
/-- `headsDistinct`, in the form the argument actually uses: a token heads at most one operator. -/
theorem head_inj {e : G.Ent} {o o' : (G.entry e).Op} {t : Tok}
    (h : ((G.entry e).operator o).headTok? = some t)
    (h' : ((G.entry e).operator o').headTok? = some t) : o = o' :=
  (G.entry e).headsDistinct o o' (by rw [h]; rfl) (by rw [h, h'])

/-- **A hole-led operator's head token starts no operand.** It is not a variable (`varDisjoint`),
and the only operator it heads is the hole-led one itself (`headsDistinct`). -/
theorem not_startsOperand_of_head {e : G.Ent} {o : (G.entry e).Op} {t : Tok}
    (hhole : ((G.entry e).operator o).startsWithHole = true)
    (hhead : ((G.entry e).operator o).headTok? = some t) : startsOperand e t = false := by
  have hnv : (G.entry e).isVar t = false :=
    (G.entry e).varDisjoint o t (Operator.headTok?_mem _ hhead)
  cases hs : startsOperand e t with
  | false => rfl
  | true =>
      exfalso
      simp only [startsOperand, hnv, Bool.false_or, List.any_eq_true] at hs
      obtain ⟨o', -, ho'⟩ := hs
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at ho'
      obtain ⟨hnh, hm⟩ := ho'
      revert hm
      cases hk : ((G.entry e).operator o').headTok? with
      | none => simp
      | some a =>
          intro hm
          -- The ancestor's token type was a `String` subtype with `BEq`, so `beq_iff_eq` applied
          -- and a `Subtype.ext` fallback was needed. Over an abstract `Tok` the membership test
          -- goes through `DecidableEq`, so the hypothesis arrives as `decide (a = t) = true`.
          have ht : a = t := of_decide_eq_true hm
          have hoo : o' = o := head_inj (by rw [hk, ht]) hhead
          rw [hoo, hhole] at hnh
          simp at hnh

/-! ★ `not_continuesAt_tighter_head` — a hole-led operator's own head token does not continue an
expression at `.tighter o` — is already in `Complete.lean`, proved there from scratch in `2845d9d`.
This file's ancestor is where it came from; only the `juxt` companion below is new. -/

/-- ★ The `juxt` analogue: an **operand-starting** token does not continue at `.tighter j` when `j`
is juxtaposition. Juxtaposition strictly tighter than itself is impossible (`juxtUnique` +
`Tighter.irrefl`), and an operand-starter heads no hole-led operator. -/
theorem not_continuesAt_tighter_juxt {e : G.Ent} {j : (G.entry e).Op} {t : Tok}
    (hj : (G.entry e).operator j = Operator.juxt)
    (hstart : startsOperand e t = true) :
    ¬ ContinuesAt e (.tighter j) t := by
  rintro (⟨o', hc', hhole', hhead'⟩ | ⟨j', hc', hj', -⟩)
  · rw [not_startsOperand_of_head hhole' hhead'] at hstart; exact absurd hstart (by simp)
  · exact Tighter.irrefl ((G.entry e).juxtUnique j' j hj' hj ▸ hc')


/-! ## The spine view

`infxl` and `juxt` are exactly the operators whose body leads with a `.tighterEq` hole
(`Operator.leftRec`). For those, a tree at `.tighterEq o` unfolds into

    base : Expr e (.tighter o)          -- STRICTLY tighter: not `o`-headed
    tails : List (Parts G (body e o).tail)

and that normal form is what makes the kernel true (see the note above). -/

omit [DecidableEq Tok] in
/-- A left-recursive body leads with a `.tighterEq o` hole at the host entry. -/
theorem body_leftRec_cons {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) :
    Operator.body e o = .hole e (.tighterEq o) :: (Operator.body e o).tail := by
  cases hop : (G.entry e).operator o with
  | infxl n => unfold Operator.body; rw [hop]; rfl
  | juxt    => unfold Operator.body; rw [hop]; rfl
  | closed n => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | prefx n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infx n   => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infxr n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | postfx n => rw [hop] at hlr; simp [Operator.leftRec] at hlr

/-- **The left-recursive smart constructor**, uniform over `infxl` and `juxt`
(generalising `Expr.juxtApp` / `Expr.infxlApp`). -/
def Expr.leftRecApp {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true)
    (L : Expr G e (Level.tighterEq o)) (T : Parts G (Operator.body e o).tail) :
    Expr G e (Level.tighterEq o) :=
  Expr.op o TighterEq.refl ((body_leftRec_cons hlr).symm ▸ Parts.hole L T)

omit [DecidableEq Tok] in
/-- Its flattening is the concatenation, as it must be. -/
theorem Expr.leftRecApp_flatten {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true)
    (L : Expr G e (Level.tighterEq o)) (T : Parts G (Operator.body e o).tail) :
    (Expr.leftRecApp hlr L T).flatten = L.flatten ++ T.flatten := by
  rw [Expr.leftRecApp, Expr.flatten, Parts.flatten_cast, Parts.flatten]

/-- Cast cancellation, stated over *variables* so that `cases h` is available (the shape equations
we actually have — `Operator.body e o = …` — have no variable side, so they cannot be `cases`d
directly). -/
theorem cast_eq_iff {α : Sort _} {P : α → Sort _} {a b : α} (h : a = b) (x : P a) (y : P b) :
    (h ▸ x) = y ↔ x = (h.symm ▸ y) := by cases h; simp

omit [DecidableEq Tok] in
/-- **Inversion**: every body of a left-recursive operator splits into its left operand and tail,
and the left operand is strictly smaller. -/
theorem Parts.leftRec_inv {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    ∃ (L : Expr G e (Level.tighterEq o)) (T : Parts G (Operator.body e o).tail),
      ps = (body_leftRec_cons hlr).symm ▸ Parts.hole L T ∧
        ps.flatten = L.flatten ++ T.flatten ∧ L.size < ps.size := by
  have hb := body_leftRec_cons hlr
  cases hq : (hb ▸ ps : Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | hole L T =>
      refine ⟨L, T, (cast_eq_iff hb ps _).mp hq, ?_, ?_⟩
      · rw [← Parts.flatten_cast hb ps, hq, Parts.flatten]
      · rw [← Parts.size_cast hb ps, hq, Parts.size]; omega


/-! ### Destructors, and the unfold -/

/-- The left operand of a left-recursive body. -/
def Parts.leftRecL {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    Expr G e (Level.tighterEq o) :=
  match (body_leftRec_cons hlr ▸ ps :
      Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | .hole L _ => L

/-- The tail of a left-recursive body. -/
def Parts.leftRecT {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    Parts G (Operator.body e o).tail :=
  match (body_leftRec_cons hlr ▸ ps :
      Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | .hole _ T => T

omit [DecidableEq Tok] in
theorem Parts.leftRec_eta {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    ps = (body_leftRec_cons hlr).symm ▸ Parts.hole (ps.leftRecL hlr) (ps.leftRecT hlr) := by
  have hb := body_leftRec_cons hlr
  rw [← cast_eq_iff hb ps]
  unfold Parts.leftRecL Parts.leftRecT
  cases (hb ▸ ps : Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | hole L T => rfl

omit [DecidableEq Tok] in
theorem Parts.leftRec_flatten {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    ps.flatten = (ps.leftRecL hlr).flatten ++ (ps.leftRecT hlr).flatten := by
  have hb := body_leftRec_cons hlr
  rw [← Parts.flatten_cast hb ps]
  unfold Parts.leftRecL Parts.leftRecT
  cases (hb ▸ ps : Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | hole L T => rfl

omit [DecidableEq Tok] in
theorem Parts.leftRecL_size {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    (ps.leftRecL hlr).size < ps.size := by
  have hb := body_leftRec_cons hlr
  rw [← Parts.size_cast hb ps]
  unfold Parts.leftRecL
  cases (hb ▸ ps : Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | hole L T =>
      show L.size < (Parts.hole L T).size
      simp only [Parts.size]
      omega

omit [DecidableEq Tok] in
/-- Transporting a body along an operator equation does not change its size. -/
theorem Parts.size_opCast {e : G.Ent} {o o' : (G.entry e).Op} (h : o' = o)
    (ps : Parts G (Operator.body e o')) : (h ▸ ps : Parts G (Operator.body e o)).size = ps.size := by
  cases h; rfl

omit [DecidableEq Tok] in
theorem Parts.flatten_opCast {e : G.Ent} {o o' : (G.entry e).Op} (h : o' = o)
    (ps : Parts G (Operator.body e o')) :
    (h ▸ ps : Parts G (Operator.body e o)).flatten = ps.flatten := by
  cases h; rfl

open Classical in
/-- **The spine unfold.** A tree at `.tighterEq o` becomes a *strictly tighter* base plus the list
of body tails hanging off it, in left-to-right order. `n = 0` exactly when the top operator is not
`o`. -/
noncomputable def Expr.spine {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) :
    Expr G e (Level.tighterEq o) →
      Expr G e (Level.tighter o) × List (Parts G (Operator.body e o).tail)
  | .var t hv => (.var t hv, [])
  | .op o' hc ps =>
      if h : o' = o then
        let sp := Expr.spine hlr ((h ▸ ps : Parts G (Operator.body e o)).leftRecL hlr)
        (sp.1, sp.2 ++ [(h ▸ ps : Parts G (Operator.body e o)).leftRecT hlr])
      else
        -- `o'` inhabits `.tighterEq o` and is not `o`, so it is STRICTLY tighter
        (.op o' (by
            rcases TighterEq.toTighterOrEq hc with heq | hT
            · exact absurd heq.symm h
            · exact hT) ps, [])
  termination_by t => t.size
  decreasing_by
    simp_wf
    have h1 := Parts.leftRecL_size hlr (h ▸ ps : Parts G (Operator.body e o))
    have h2 := Parts.size_opCast h ps
    simp only [Expr.size]
    omega


omit [DecidableEq Tok] in
/-- **The spine flattens to base ++ tails.** -/
theorem Expr.spine_flatten {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (t : Expr G e (Level.tighterEq o)) :
    t.flatten = (Expr.spine hlr t).1.flatten
      ++ (((Expr.spine hlr t).2).map Parts.flatten).flatten := by
  induction t using Expr.spine.induct (hlr := hlr) with
  | case1 tk hv => simp [Expr.spine, Expr.flatten]
  | case2 hc ps ih =>
      rw [Expr.spine, dif_pos (rfl : o = o)]
      rw [Expr.flatten]
      rw [Parts.leftRec_flatten hlr ps] at *
      rw [ih]
      simp [List.map_append, List.append_assoc]
  | case3 o' hc ps hne =>
      rw [Expr.spine, dif_neg hne]
      simp [Expr.flatten]

/-! ## The spine: what the `infxl`/`juxt` kernel must actually say

The ★ lemmas make FOLLOW available at `.tighter o`. What remains is to get the *shape* of the
statement right, and two natural attempts are **FALSE**. Both counterexamples use `o = +` (infxl),
`s` a leftover stopping the ambient level `l`.

**Attempt 1** — "left operands with FOLLOW-stopping continuations agree":
    L₁ = `a`,     c₁ = `+ b`        L₂ = `a + b`,  c₂ = `[]`
Both `c`s satisfy `FollowAt e (.tighter o)` (`+` does not continue there, by ★; `[]` vacuously),
the flattenings agree — and `L₁ ≠ L₂`. The hypothesis is too weak: it does not know that `c` is a
*body tail followed by a stopping leftover*.

**Attempt 2** — repair it by letting `c` be *any* sequence of body tails then a stopping leftover
(`TailSeq`). Still false:
    L₁ = `a + b`, c₁ = `+ c ++ s`   L₂ = `a`,      c₂ = `+ b + c ++ s`
Both `c`s are legitimate tail-sequences (`c₂` is two tails), the flattenings agree, `L₁ ≠ L₂`. The
*number of tails* is doing real work and cannot be existentially quantified away.

**The correct statement.** Normalise the spine. Every tree at `.tighterEq o` is uniquely

    base + [tail₁, …, tailₙ]        base : Expr e (.tighter o)   -- STRICTLY tighter
                                    tailᵢ : Parts (Operator.body e o).tail

with `n = 0` exactly when the top operator is not `o` (`TighterEq.toTighterOrEq`: a top operator at
`.tighterEq o` is either `o` itself or strictly tighter — and a `var` inhabits every level). The
base is at `.tighter o`, **not** `.tighterEq o`; that is the whole point, and it is what kills
Attempt 2, whose `L₂ = a` could absorb an extra tail precisely because `a + b` was allowed to be a
"base".

Uniqueness then falls out of the ★ lemmas:
* compare `base₁` and `base₂` at `.tighter o`. Their continuations start with `headTok o` (if any
  tail remains) or are the final leftover — `FollowAt e (.tighter o)` holds in both cases, by ★ and
  by `FollowAt.tighten` respectively. So `udExpr` at `.tighter o` applies;
* compare the tails one at a time with `udParts`. A tail's right operand sits at `.tighter o` and
  its continuation is again "next tail, or the leftover" — same argument;
* when one spine runs out first, its leftover **stops `l`** while the other still begins with
  `headTok o`, which **continues** `l` (`o` is applicable at `l`). Contradiction. This is the step
  that forces the two spines to have the same length, and it is the only place the *ambient* level
  is used.

## Where the kernel actually stands (2026-08-13)

The spine view above is built. Of the three kernel obligations this file's ancestor carried:

* **`varOp_ne` — CLOSED**, and without the spine. A variable leaf is one token, so an operator
  node sharing its first token must overrun it, and `op_var_head` names the token that does the
  overrunning: `varDisjoint` if the operator is token-led, otherwise a descent into its leading
  hole, bottoming out at a variable leaf where `holeLed_split` applies.
* **`topOp_unique` — half closed.** Token-led vs token-led is `headsDistinct`
  (`topOp_unique_tokenLed`). The rest is `topOp_unique_holeLed`, still open; its docstring records
  why it cannot be peeled off the way `varOp_ne` was.
* **`splitLeftRec` — replaced** by `udPartsAux`, an induction on the *shape* (the operator it came
  from is irrelevant). Empty and name-part cases are proved; only the hole case is open, and it is
  open for one precise reason: it is a call to `udExpr`.

So both remaining gaps are the same gap — `udExpr` and `udPartsAux` need to be one `mutual` block,
terminating on summed sizes, with the leading `.tighterEq` hole of a left-recursive operator routed
through `Expr.spine` first (that hole is the one case where neither ★ lemma gives FOLLOW). -/

/-! ### The token-led halves, which need no induction

`topOp_unique` and `varOp_ne` each split on whether the operator's body leads with its own token or
with a hole. The **token-led** half is immediate from the two lexical fields, and is proved here
once so that the remaining kernel obligations are about hole-led operators only. -/

omit [DecidableEq Tok] in
/-- A token-led body flattens to its head token followed by the rest. -/
theorem Parts.flatten_tokenLed {e : G.Ent} {o : (G.entry e).Op}
    (hnh : ((G.entry e).operator o).startsWithHole = false)
    (p : Parts G (Operator.body e o)) :
    ∃ tk r, p.flatten = tk :: r ∧ ((G.entry e).operator o).headTok? = some tk := by
  obtain ⟨tk, ps, hb, hhead⟩ := body_cons_namePart o hnh
  obtain ⟨r, hr⟩ := Parts.flatten_cons_namePart (hb ▸ p)
  exact ⟨tk, r, by rw [← Parts.flatten_cast hb p, hr], hhead⟩

omit [DecidableEq Tok] in
/-- **The token-led half of `varOp_ne`.** A variable leaf and a token-led operator cannot share a
first token, because that token would be both a variable and an operator name part — exactly what
`varDisjoint` forbids. No induction, no FOLLOW. -/
theorem varOp_ne_tokenLed {e : G.Ent} {t : Tok}
    (hv : (G.entry e).isVar t = true) {o : (G.entry e).Op}
    (hnh : ((G.entry e).operator o).startsWithHole = false)
    (p : Parts G (Operator.body e o)) (s₁ s₂ : List Tok)
    (heq : [t] ++ s₁ = p.flatten ++ s₂) : False := by
  obtain ⟨tk, r, hpf, hhead⟩ := Parts.flatten_tokenLed hnh p
  rw [hpf] at heq
  have htk : t = tk := by simpa using congrArg List.head? heq
  have : (G.entry e).isVar tk = false :=
    (G.entry e).varDisjoint o tk (Operator.headTok?_mem _ hhead)
  rw [htk, this] at hv
  exact Bool.noConfusion hv

omit [DecidableEq Tok] in
/-- **The token-led half of `topOp_unique`.** Two token-led operators whose flattenings agree share
a head token, and `headsDistinct` says that makes them the same operator. -/
theorem topOp_unique_tokenLed {e : G.Ent} {o₁ o₂ : (G.entry e).Op} (hne : o₁ ≠ o₂)
    (hnh₁ : ((G.entry e).operator o₁).startsWithHole = false)
    (hnh₂ : ((G.entry e).operator o₂).startsWithHole = false)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List Tok)
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂) : False := by
  obtain ⟨tk₁, r₁, hpf₁, hhead₁⟩ := Parts.flatten_tokenLed hnh₁ p₁
  obtain ⟨tk₂, r₂, hpf₂, hhead₂⟩ := Parts.flatten_tokenLed hnh₂ p₂
  rw [hpf₁, hpf₂] at heq
  have htk : tk₁ = tk₂ := by simpa using congrArg List.head? heq
  exact hne (head_inj hhead₁ (htk ▸ hhead₂))

/-! ### Hole-led operators: what sits immediately after the leading operand

The remaining halves are about an operator whose body *leads with a hole*. The fact that drives
them: after that leading operand comes a token which **continues an expression at any level where
the operator is applicable** — the operator's own head token for `infx`/`infxl`/`infxr`/`postfx`,
and, for `juxt` (which owns no token), the first token of the right operand, which starts an
operand. That is exactly the two disjuncts of `ContinuesAt`. -/

/-- `ContinuesAt` is monotone in the level: widening which operators are applicable can only add
ways for a token to continue. (`ContinuesAt` itself decides token equality through
`startsOperand`, so this one keeps `DecidableEq Tok`.) -/
theorem ContinuesAt.mono {e : G.Ent} {l L : Level (G.entry e)} {x : Tok}
    (hup : ∀ o', Level.condition L o' → Level.condition l o')
    (h : ContinuesAt e L x) : ContinuesAt e l x := by
  rcases h with ⟨o', hc', hh', hd'⟩ | ⟨j, hc', hj', hs'⟩
  · exact Or.inl ⟨o', hup _ hc', hh', hd'⟩
  · exact Or.inr ⟨j, hup _ hc', hj', hs'⟩

omit [DecidableEq Tok] in
/-- An operand hole sits at `.tighter o` or `.tighterEq o`; either way everything applicable there
is applicable wherever `o` is. -/
theorem condition_up_tighter {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) :
    ∀ o', Level.condition (Level.tighter o) o' → Level.condition l o' :=
  fun _ h => Level.condition_up hc h.toTighterEq'

omit [DecidableEq Tok] in
theorem condition_up_tighterEq {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) :
    ∀ o', Level.condition (Level.tighterEq o) o' → Level.condition l o' :=
  fun _ h => Level.condition_up hc h

/-- **The split, for the four token-bearing hole-led fixities.** Their bodies all have the shape
`hole :: (notation ++ suffix)`, and a notation always leads with its first token — which is the
operator's head token, hence continues wherever the operator is applicable. -/
theorem holeLed_split_named {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (hh : ((G.entry e).operator o).startsWithHole = true)
    {L : Level (G.entry e)} {n : Notation Tok G.Ent} {suffix : List (Part G)}
    (hb : Operator.body e o = .hole e L :: (Notation.toParts n ++ suffix))
    (hhead : ((G.entry e).operator o).headTok? = some n.firstTok)
    (hup : ∀ o', Level.condition L o' → Level.condition l o')
    (p : Parts G (Operator.body e o)) :
    ∃ (L' : Level (G.entry e)) (sub : Expr G e L') (x : Tok) (w : List Tok),
      p.flatten = sub.flatten ++ x :: w ∧ sub.size < p.size ∧ ContinuesAt e l x ∧
        (∀ o', Level.condition L' o' → Level.condition l o') := by
  -- destructure the leading hole
  cases hq : (hb ▸ p : Parts G (.hole e L :: (Notation.toParts n ++ suffix))) with
  | hole sub q =>
      -- and the notation's first token, which `toParts` always exposes
      have hn := Notation.toParts_append_cons (G := G) n suffix
      cases hq' : (hn ▸ q : Parts G (.namePart n.firstTok ::
          ((Notation.toParts (G := G) n).tail ++ suffix))) with
      | namePart _ q' =>
          have hqf : q.flatten = n.firstTok :: q'.flatten := by
            rw [← Parts.flatten_cast hn q, hq', Parts.flatten]
          refine ⟨L, sub, n.firstTok, q'.flatten, ?_, ?_, Or.inl ⟨o, hc, hh, hhead⟩, hup⟩
          · rw [← Parts.flatten_cast hb p, hq, Parts.flatten, hqf]
          · rw [← Parts.size_cast hb p, hq, Parts.size]
            omega

/-- **After a hole-led operator's leading operand comes a token that continues the expression.**
Uniform over all five hole-led fixities. `juxt` is the case that has to be done by hand: owning no
token, it continues through its *right operand*, so the witness comes from
`Expr.flatten_head` and lands in `ContinuesAt`'s second disjunct rather than its first. -/
theorem holeLed_split {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (hh : ((G.entry e).operator o).startsWithHole = true)
    (p : Parts G (Operator.body e o)) :
    ∃ (L' : Level (G.entry e)) (sub : Expr G e L') (x : Tok) (w : List Tok),
      p.flatten = sub.flatten ++ x :: w ∧ sub.size < p.size ∧ ContinuesAt e l x ∧
        (∀ o', Level.condition L' o' → Level.condition l o') := by
  cases hop : (G.entry e).operator o with
  | closed n => rw [hop] at hh; simp [Operator.startsWithHole] at hh
  | prefx n  => rw [hop] at hh; simp [Operator.startsWithHole] at hh
  | infx n =>
      refine holeLed_split_named hc hh (L := Level.tighter o) (n := n)
        (suffix := [.hole e (Level.tighter o)]) ?_ ?_ (condition_up_tighter hc) p
      · unfold Operator.body; rw [hop]; rfl
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | infxl n =>
      refine holeLed_split_named hc hh (L := Level.tighterEq o) (n := n)
        (suffix := [.hole e (Level.tighter o)]) ?_ ?_ (condition_up_tighterEq hc) p
      · unfold Operator.body; rw [hop]; rfl
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | infxr n =>
      refine holeLed_split_named hc hh (L := Level.tighter o) (n := n)
        (suffix := [.hole e (Level.tighterEq o)]) ?_ ?_ (condition_up_tighter hc) p
      · unfold Operator.body; rw [hop]; rfl
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | postfx n =>
      refine holeLed_split_named hc hh (L := Level.tighter o) (n := n)
        (suffix := []) ?_ ?_ (condition_up_tighter hc) p
      · unfold Operator.body; rw [hop]; simp
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | juxt =>
      have hb : Operator.body e o
          = .hole e (Level.tighterEq o) :: [.hole e (Level.tighter o)] := by
        -- `rw` closes this one by itself: unlike the `[x] ++ ys` fixities, the juxt body is
        -- already syntactically a cons
        unfold Operator.body; rw [hop]
      cases hq : (hb ▸ p : Parts G (.hole e (Level.tighterEq o) ::
          [.hole e (Level.tighter o)])) with
      | hole sub q =>
          cases hq' : q with
          | hole sub₂ tl =>
              -- juxtaposition continues through its right operand, whose first token starts one
              obtain ⟨x, r, hxr, hstart⟩ := Expr.flatten_head sub₂
              refine ⟨Level.tighterEq o, sub, x, r ++ tl.flatten, ?_, ?_,
                Or.inr ⟨o, hc, hop, hstart⟩, condition_up_tighterEq hc⟩
              · rw [← Parts.flatten_cast hb p, hq, Parts.flatten, hq', Parts.flatten, hxr]
                simp
              · rw [← Parts.size_cast hb p, hq, Parts.size]
                omega

/-- **An operator tree that begins with a variable token is continued right after it.**

This is the leftmost descent, and it is what makes `varOp_ne` provable *without* the full mutual
decomposition. If an operator node's flattening starts with a variable token, the operator cannot
be token-led (`varDisjoint`), so it leads with a hole; the variable is then the first token of that
hole's subtree, and we recurse into it. The descent bottoms out at a variable leaf, at which point
`holeLed_split` supplies the continuing token. Each step drops a whole `Parts` node, so the
recursion is on `p.size`.

The level travels with the recursion: the token found inside a hole continues at the *hole's*
level, and `ContinuesAt.mono` lifts that to the ambient one, because an operand hole is never
looser than its operator. -/
theorem op_var_head {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (p : Parts G (Operator.body e o))
    {t : Tok} {w : List Tok} (hv : (G.entry e).isVar t = true)
    (hf : p.flatten = t :: w) :
    ∃ x r, w = x :: r ∧ ContinuesAt e l x := by
  cases hnh : ((G.entry e).operator o).startsWithHole with
  | false =>
      exact absurd (varOp_ne_tokenLed hv hnh p w [] (by simp [hf])) (fun h => h)
  | true =>
      obtain ⟨L', sub, x, w', hsplit, hsize, hcont, hup⟩ := holeLed_split hc hnh p
      rw [hf] at hsplit
      cases sub with
      | var t' hv' =>
          -- the descent bottoms out: the variable *is* the whole leading operand
          simp only [Expr.flatten, List.cons_append, List.nil_append,
            List.cons.injEq] at hsplit
          exact ⟨x, w', hsplit.2, hcont⟩
      | op o'' hc'' p'' =>
          simp only [Expr.flatten] at hsplit hsize
          -- the leading operand is itself an operator node, and it too starts with `t`
          obtain ⟨a, as, has⟩ : ∃ a as, p''.flatten = a :: as := by
            cases hpf : p''.flatten with
            | nil => exact absurd hpf (Parts.flatten_ne_nil p'' (Operator.body_ne_nil o''))
            | cons a as => exact ⟨a, as, rfl⟩
          rw [has] at hsplit
          simp only [List.cons_append, List.cons.injEq] at hsplit
          obtain ⟨rfl, hw⟩ := hsplit
          obtain ⟨y, r, hyr, hcy⟩ := op_var_head hc'' p'' hv has
          exact ⟨y, r ++ x :: w', by rw [hw, hyr]; simp, ContinuesAt.mono hup hcy⟩
  termination_by p.size
  decreasing_by simp only [Expr.size] at hsize; omega

/-- **Two bodies over one shape agree** — the `udParts` content, by induction on the shape. The
empty and name-part cases are structural; the hole case is the one that calls back into `udExpr`,
and is the single remaining gap (see below). `hb` is not needed: the statement is about a shape,
not about which operator produced it. -/
theorem udPartsAux {e : G.Ent} {l : Level (G.entry e)} :
    ∀ {shape : List (Part G)} (p₁ p₂ : Parts G shape) (s₁ s₂ : List Tok),
      p₁.flatten ++ s₁ = p₂.flatten ++ s₂ → FollowAt e l s₁ → FollowAt e l s₂ →
      p₁ = p₂ ∧ s₁ = s₂ := by
  intro shape
  induction shape with
  | nil =>
      intro p₁ p₂ s₁ s₂ heq _ _
      cases p₁; cases p₂
      exact ⟨rfl, by simpa [Parts.flatten] using heq⟩
  | cons hd tl ih =>
      match hd with
      | .namePart tk =>
          intro p₁ p₂ s₁ s₂ heq hs₁ hs₂
          cases p₁ with
          | namePart _ q₁ =>
            cases p₂ with
            | namePart _ q₂ =>
              simp only [Parts.flatten, List.cons_append, List.cons.injEq] at heq
              obtain ⟨hq, hs⟩ := ih q₁ q₂ s₁ s₂ heq.2 hs₁ hs₂
              exact ⟨by rw [hq], hs⟩
      | .hole e' L =>
          intro p₁ p₂ s₁ s₂ heq hs₁ hs₂
          -- ⚠ THE ONE REMAINING GAP. `p₁ = hole sub₁ q₁`, `p₂ = hole sub₂ q₂`, and
          --   sub₁.flatten ++ (q₁.flatten ++ s₁) = sub₂.flatten ++ (q₂.flatten ++ s₂).
          -- Concluding `sub₁ = sub₂` is exactly `udExpr` at `(e', L)`, so this theorem and
          -- `udExpr` must become one `mutual` block, terminating on the summed sizes.
          -- Its two side conditions are `FollowAt e' L (qᵢ.flatten ++ sᵢ)`, supplied by:
          --   * `follow_of_interior` when `tl` starts with a name part (an interior seam);
          --   * `FollowAt.tighten` when `tl = []` (a trailing hole, so the continuation is `sᵢ`);
          --   * `not_continuesAt_tighter_head` / `not_continuesAt_tighter_juxt` for an operator's
          --     own operand seam — and for a `.tighterEq` (left-recursive) hole neither applies,
          --     which is why that case must first be normalised through `Expr.spine`.
          sorry

/-- **The remaining half of `topOp_unique`**: at least one of the two operators leads with a hole.

Why this one cannot be peeled off the way `varOp_ne` was. There, the competing tree was a variable
*leaf* — one token — so the operator tree was strictly longer and `op_var_head` could name the
token that overran. Here both competitors are operator nodes of unknown extent, and both
flattenings begin with a token that starts an operand: a token-led operator's head starts one by
definition, and a hole-led operator inherits one from its leading operand
(`Expr.flatten_head`). Nothing local separates them.

The separating fact is which of the two extents is the shorter — and that is precisely unique
decomposition, so this case has to be discharged *inside* the `udExpr`/`udParts` recursion rather
than before it. Comparing the token-led tree against the hole-led one's leading operand does not
help either: that operand sits at a tighter level `L`, and the token following it continues at `l`
(`holeLed_split`), so `udExpr` at `l` has no FOLLOW to work with, while at `L` the token-led tree
need not even be typeable. -/
theorem topOp_unique_holeLed {e : G.Ent} {l : Level (G.entry e)} {o₁ o₂ : (G.entry e).Op}
    (hne : o₁ ≠ o₂) (hc₁ : Level.condition l o₁) (hc₂ : Level.condition l o₂)
    (hhole : ((G.entry e).operator o₁).startsWithHole = true ∨
             ((G.entry e).operator o₂).startsWithHole = true)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List (Tok))
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : False := by
  sorry

/-- **Two distinct top operators cannot share a flattening.** The token-led/token-led case is
`headsDistinct` outright; everything else is `topOp_unique_holeLed`. -/
theorem topOp_unique {e : G.Ent} {l : Level (G.entry e)} {o₁ o₂ : (G.entry e).Op}
    (hne : o₁ ≠ o₂) (hc₁ : Level.condition l o₁) (hc₂ : Level.condition l o₂)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List (Tok))
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : False := by
  cases hnh₁ : ((G.entry e).operator o₁).startsWithHole with
  | true => exact topOp_unique_holeLed hne hc₁ hc₂ (Or.inl hnh₁) p₁ p₂ s₁ s₂ heq hs₁ hs₂
  | false =>
      cases hnh₂ : ((G.entry e).operator o₂).startsWithHole with
      | true => exact topOp_unique_holeLed hne hc₁ hc₂ (Or.inr hnh₂) p₁ p₂ s₁ s₂ heq hs₁ hs₂
      | false => exact topOp_unique_tokenLed hne hnh₁ hnh₂ p₁ p₂ s₁ s₂ heq

/-- **A variable and an operator cannot share a flattening.** ✅ *Closed.*

A variable leaf prints one token, so if an operator node's flattening starts with it, the operator
tree runs strictly longer — and `op_var_head` says the very next token continues an expression at
`l`. That token heads `s₁`, which `FollowAt e l s₁` forbids. Both fixity families are handled:
token-led inside `op_var_head` by `varDisjoint`, hole-led by the descent. -/
theorem varOp_ne {e : G.Ent} {l : Level (G.entry e)} {t : Tok}
    (hv : (G.entry e).isVar t = true) {o : (G.entry e).Op} (hc : Level.condition l o)
    (p : Parts G (Operator.body e o)) (s₁ s₂ : List (Tok))
    (heq : [t] ++ s₁ = p.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (_hs₂ : FollowAt e l s₂) : False := by
  obtain ⟨a, as, has⟩ : ∃ a as, p.flatten = a :: as := by
    cases hpf : p.flatten with
    | nil => exact absurd hpf (Parts.flatten_ne_nil p (Operator.body_ne_nil o))
    | cons a as => exact ⟨a, as, rfl⟩
  rw [has] at heq
  simp only [List.cons_append, List.cons.injEq] at heq
  obtain ⟨rfl, hs⟩ := heq
  obtain ⟨x, r, hxr, hcont⟩ := op_var_head hc p hv has
  have hs' : s₁ = as ++ s₂ := by simpa using hs
  exact hs₁ x (by rw [hs', hxr]; rfl) hcont

/-! ## The mutual unique decomposition

⚠ Neither theorem below is *currently* recursive: `udParts` delegates straight to the sorried
`splitLeftRec`, so the `termination_by` clauses the ancestor carried
(`t₁.size + t₂.size` for `udExpr`, `p₁.size + p₂.size` for `udParts`) are flagged unused and are
dropped to keep the build warning-clean. **Put them back when `splitLeftRec` is replaced by the
spine argument** — that is what makes `udParts` call back into `udExpr`, and the measure is what
justifies it. -/

mutual
  /-- Two expressions at the same level whose flattenings agree up to leftovers that **stop** the
  level are equal, with equal leftovers. -/
  theorem udExpr (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l)
      (s₁ s₂ : List (Tok))
      (heq : t₁.flatten ++ s₁ = t₂.flatten ++ s₂)
      (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
    match t₁, t₂ with
    | .var a ha, .var b hb =>
        simp only [Expr.flatten, List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, hs⟩ := heq
        exact ⟨rfl, hs⟩
    | .var a ha, .op o c p =>
        exact absurd heq (fun h => (varOp_ne ha c p s₁ s₂ (by simpa [Expr.flatten] using h)
          hs₁ hs₂).elim)
    | .op o c p, .var b hb =>
        exact absurd heq (fun h => (varOp_ne hb c p s₂ s₁ (by simpa [Expr.flatten] using h.symm)
          hs₂ hs₁).elim)
    | .op o₁ c₁ p₁, .op o₂ c₂ p₂ =>
        by_cases ho : o₁ = o₂
        · subst ho
          have hpe : p₁.flatten ++ s₁ = p₂.flatten ++ s₂ := by
            simpa only [Expr.flatten] using heq
          obtain ⟨hp, hss⟩ := udParts e l o₁ c₁ rfl p₁ p₂ s₁ s₂ hpe hs₁ hs₂
          exact ⟨by rw [hp], hss⟩
        · exact absurd heq (fun h => (topOp_unique ho c₁ c₂ p₁ p₂ s₁ s₂
            (by simpa only [Expr.flatten] using h) hs₁ hs₂).elim)

  /-- Two bodies of the **same** operator, over the same shape, with a common flatten-prefix. -/
  theorem udParts (e : G.Ent) (l : Level (G.entry e)) (o : (G.entry e).Op)
      (_hc : Level.condition l o)
      {shape : List (Part G)} (_hb : Operator.body e o = shape)
      (p₁ p₂ : Parts G shape) (s₁ s₂ : List (Tok))
      (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : p₁ = p₂ ∧ s₁ = s₂ :=
    udPartsAux p₁ p₂ s₁ s₂ heq hs₁ hs₂
end

/-! ## The payoff -/

/-! `Unambiguous` itself is `Complete.lean`'s — the definition this file's ancestor carried is
the same one, word for word, so the port drops its copy and proves the imported predicate. -/

/-- **Unambiguity, derived.** The `rest = []` instance of unique decomposition: `[]` stops every
level vacuously, so two trees with equal flattenings are equal. No hypothesis on the grammar beyond
the three it already carries. -/
theorem unambiguous (G : Grammar Tok) : Unambiguous G := by
  intro e l t₁ t₂ hf
  refine (udExpr e l t₁ t₂ [] [] (by simpa using hf) ?_ ?_).1 <;>
    intro t ht <;> simp at ht

end LambdaLab.Parser.IsoParser.Mixfix
