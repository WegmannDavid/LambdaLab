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
carry no `o` at its top. That is what `leftRecUd` does, by descending the chain and comparing the
two spines; see "The left-recursive kernel" below.

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
`o`.

The kernel (`leftRecUd`) does **not** call this: unfolding one tree at a time would then need the
unfold to be *injective*, i.e. a reconstruction lemma. Accumulating the tails and concluding about
the refold (`Expr.leftRecFold`) gets that for free. This stays as the explicit normal form the
argument is *about* — `spine_flatten` is the law it factors through. -/
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

## Where the kernel actually stands (2026-08-14)

Of the three obligations this file's ancestor carried, **one is left**:

* **`varOp_ne` — CLOSED**, and without the spine. A variable leaf is one token, so an operator
  node sharing its first token must overrun it, and `op_var_head` names the token that does:
  `varDisjoint` if the operator is token-led, otherwise a descent into its leading hole, bottoming
  out at a variable leaf where `holeLed_split` applies.
* **`udExpr`/`udParts` are now one `mutual`** on an explicit size bound, and **`udParts` is
  closed** — including its hole case, which is the call back into `udExpr` at the hole's own entry
  and level. Its two side conditions come from `Seamed`/`PartsFollow`, which is what a *shape* can
  supply: a shape constrains what follows it only through a trailing hole and its interior only at
  the seams.
* **The `leftRec` branch of `udExprN` — CLOSED**, by `leftRecUd` (below `partsFollow_body`).
  `infxl`/`juxt` bodies are not `Seamed`, so `udParts` cannot touch them; the branch hands both
  bodies to a spine descent instead. The descent carries the peeled-off tails in an accumulator and
  concludes about the **refold** (`Expr.leftRecFold`), which the peeling leaves invariant — so
  `Expr.spine` is not used and no spine-injectivity lemma is needed. It bottoms out at two
  non-`o`-headed trees, which are trees at `.tighter o` (`leftRec_view`, `Expr.decomp`), where ★
  restores FOLLOW.
* **One gap remains**: `topOp_unique_holeLed` — two *distinct* operators, at least one hole-led.
  See its docstring: the separating fact is which extent is shorter, so it belongs inside the
  recursion. It is no longer about left-recursion at all. -/

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

omit [DecidableEq Tok] in
/-- A tighter-or-equal path composed with a strictly tighter one stays strict — the mirror of
`Tighter.trans_tighterEq`, and what lets a fact about `.tighter o` be pushed down to `.tighter o'`
for any `o'` the leading hole admits. -/
theorem Tighter.of_tighterEq {Op : Type} {t : Op → List Op} {a b c : Op}
    (h₁ : TighterEq t a b) (h₂ : Tighter t b c) : Tighter t a c := by
  revert h₂
  induction h₁ with
  | refl => exact id
  | step hm _ ih => exact fun h => Tighter.step hm (ih h)

/-- **The split, for the four token-bearing hole-led fixities.** Their bodies all have the shape
`hole :: (notation ++ suffix)`, and a notation always leads with its first token — which is the
operator's head token, hence continues wherever the operator is applicable.

The last conjunct is the one the *distinct-operator* case needs: the token does not continue at
`.tighter o'` for **any** `o'` the leading hole admits. That is ★ pushed one step down — an operator
inhabiting the leading hole is tighter-or-equal to `o` (`hle`), so continuing below it would be
continuing below `o`. -/
theorem holeLed_split_named {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (hh : ((G.entry e).operator o).startsWithHole = true)
    {L : Level (G.entry e)} {n : Notation Tok G.Ent} {suffix : List (Part G)}
    (hb : Operator.body e o = .hole e L :: (Notation.toParts n ++ suffix))
    (hhead : ((G.entry e).operator o).headTok? = some n.firstTok)
    (hup : ∀ o', Level.condition L o' → Level.condition l o')
    (hle : ∀ o', Level.condition L o' → TighterEq (G.entry e).tighter o o')
    (p : Parts G (Operator.body e o)) :
    ∃ (L' : Level (G.entry e)) (sub : Expr G e L') (x : Tok) (w : List Tok),
      p.flatten = sub.flatten ++ x :: w ∧ sub.size < p.size ∧ ContinuesAt e l x ∧
        (∀ o', Level.condition L' o' → Level.condition l o') ∧
        (∀ o', Level.condition L' o' → ¬ ContinuesAt e (Level.tighter o') x) := by
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
          refine ⟨L, sub, n.firstTok, q'.flatten, ?_, ?_, Or.inl ⟨o, hc, hh, hhead⟩, hup,
            fun o' hc' hcon => not_continuesAt_tighter_head hh hhead
              (ContinuesAt.mono (L := Level.tighter o') (l := Level.tighter o)
                (fun _ h₃ => Tighter.of_tighterEq (hle o' hc') h₃) hcon)⟩
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
        (∀ o', Level.condition L' o' → Level.condition l o') ∧
        (∀ o', Level.condition L' o' → ¬ ContinuesAt e (Level.tighter o') x) := by
  cases hop : (G.entry e).operator o with
  | closed n => rw [hop] at hh; simp [Operator.startsWithHole] at hh
  | prefx n  => rw [hop] at hh; simp [Operator.startsWithHole] at hh
  | infx n =>
      refine holeLed_split_named hc hh (L := Level.tighter o) (n := n)
        (suffix := [.hole e (Level.tighter o)]) ?_ ?_ (condition_up_tighter hc)
        (fun _ h => Tighter.toTighterEq' h) p
      · unfold Operator.body; rw [hop]; rfl
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | infxl n =>
      refine holeLed_split_named hc hh (L := Level.tighterEq o) (n := n)
        (suffix := [.hole e (Level.tighter o)]) ?_ ?_ (condition_up_tighterEq hc)
        (fun _ h => h) p
      · unfold Operator.body; rw [hop]; rfl
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | infxr n =>
      refine holeLed_split_named hc hh (L := Level.tighter o) (n := n)
        (suffix := [.hole e (Level.tighterEq o)]) ?_ ?_ (condition_up_tighter hc)
        (fun _ h => Tighter.toTighterEq' h) p
      · unfold Operator.body; rw [hop]; rfl
      · rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
  | postfx n =>
      refine holeLed_split_named hc hh (L := Level.tighter o) (n := n)
        (suffix := []) ?_ ?_ (condition_up_tighter hc)
        (fun _ h => Tighter.toTighterEq' h) p
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
                Or.inr ⟨o, hc, hop, hstart⟩, condition_up_tighterEq hc,
                fun o' hc' hcon => not_continuesAt_tighter_juxt hop hstart
                  (ContinuesAt.mono (L := Level.tighter o') (l := Level.tighter o)
                    (fun _ h₃ => Tighter.of_tighterEq hc' h₃) hcon)⟩
              · rw [← Parts.flatten_cast hb p, hq, Parts.flatten, hq', Parts.flatten, hxr]
                simp
              · rw [← Parts.size_cast hb p, hq, Parts.size]
                omega

/-- **The leftmost descent.** A hole-led operator node splits as *its leftmost leaf, then a token
that continues the expression*, and the leftmost leaf is either a **variable** or a **token-led**
operator node — the only two things that can start an operand. Each step walks into the leading
hole, which drops a whole `Parts` node, so the recursion is on `p.size`.

Three things travel with it, and all three are used:

* `ContinuesAt e l x` — the token found inside a hole continues at the *hole's* level, and
  `ContinuesAt.mono` lifts that to the ambient one, because an operand hole is never looser than
  its operator;
* `¬ ContinuesAt e (.tighter u) x` for the bottom operator `u` — ★ pushed down through
  `holeLed_split`. This is the FOLLOW that lets the bottom body be compared with a competing
  token-led tree by `udParts`;
* `q.size < p.size`, so that comparison stays inside the recursion's budget. -/
theorem op_split_left {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (hh : ((G.entry e).operator o).startsWithHole = true)
    (p : Parts G (Operator.body e o)) :
    ∃ (x : Tok) (w : List Tok), ContinuesAt e l x ∧
      ((∃ (u : (G.entry e).Op) (q : Parts G (Operator.body e u)),
          ((G.entry e).operator u).startsWithHole = false ∧
          ¬ ContinuesAt e (Level.tighter u) x ∧ q.size < p.size ∧
          p.flatten = q.flatten ++ x :: w)
       ∨ (∃ t : Tok, (G.entry e).isVar t = true ∧ p.flatten = t :: x :: w)) := by
  obtain ⟨L', sub, x, w, hsplit, hsize, hcont, hup, hstop⟩ := holeLed_split hc hh p
  cases sub with
  | var t hv =>
      -- the descent bottoms out at a variable leaf
      exact ⟨x, w, hcont, Or.inr ⟨t, hv, by simpa [Expr.flatten] using hsplit⟩⟩
  | op u hcu q =>
      cases hnh : ((G.entry e).operator u).startsWithHole with
      | false =>
          -- and here at a token-led node, which is where a competing tree can be met
          simp only [Expr.flatten, Expr.size] at hsplit hsize
          exact ⟨x, w, hcont, Or.inl ⟨u, q, hnh, hstop u hcu, by omega, hsplit⟩⟩
      | true =>
          -- still hole-led: walk into it, and re-attach what this level had after it
          simp only [Expr.flatten, Expr.size] at hsplit hsize
          obtain ⟨y, r, hcy, hbot⟩ := op_split_left hcu hnh q
          refine ⟨y, r ++ x :: w, ContinuesAt.mono hup hcy, ?_⟩
          rcases hbot with ⟨u', q', hnh', hstop', hsz', hf'⟩ | ⟨t, hv, hf'⟩
          · exact Or.inl ⟨u', q', hnh', hstop', by omega, by rw [hsplit, hf']; simp⟩
          · exact Or.inr ⟨t, hv, by rw [hsplit, hf']; simp⟩
  termination_by p.size
  decreasing_by simp only [Expr.size] at hsize; omega

/-- **An operator tree that begins with a variable token is continued right after it.**

What makes `varOp_ne` provable *without* the full mutual decomposition. The leftmost descent bottoms
out either at a variable leaf — which then *is* the leading token — or at a token-led operator node,
whose first token is a name part and so cannot be the variable (`varDisjoint`). -/
theorem op_var_head {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (p : Parts G (Operator.body e o))
    {t : Tok} {w : List Tok} (hv : (G.entry e).isVar t = true)
    (hf : p.flatten = t :: w) :
    ∃ x r, w = x :: r ∧ ContinuesAt e l x := by
  cases hnh : ((G.entry e).operator o).startsWithHole with
  | false =>
      exact absurd (varOp_ne_tokenLed hv hnh p w [] (by simp [hf])) (fun h => h)
  | true =>
      obtain ⟨x, w', hcont, hbot⟩ := op_split_left hc hnh p
      rcases hbot with ⟨u, q, hnh', -, -, hf'⟩ | ⟨t', hv', hf'⟩
      · -- the bottom is token-led, so the shared first token is one of its name parts
        exfalso
        obtain ⟨tk, r, hqf, hhead⟩ := Parts.flatten_tokenLed hnh' q
        rw [hqf] at hf'
        have : t = tk := by rw [hf] at hf'; simpa using congrArg List.head? hf'
        rw [this, (G.entry e).varDisjoint u tk (Operator.headTok?_mem _ hhead)] at hv
        exact Bool.noConfusion hv
      · rw [hf] at hf'
        simp only [List.cons.injEq] at hf'
        exact ⟨x, w', hf'.2, hcont⟩


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

/-! ### `PartsFollow` for a whole operator body

`udParts` below takes `Complete.lean`'s `Seamed`/`PartsFollow` as its side conditions rather than
an ambient `FollowAt`: a shape only constrains what follows it through a *trailing* hole, and only
constrains its interior through the seams. `Seamed` for a body is `seamed_body`, already proved
there. `PartsFollow` for a body is these lemmas — the trailing hole is at `.tighter o` or
`.tighterEq o`, and `FollowAt` at the ambient level tightens to either. -/

/-- A notation's parts never end in a hole, so they constrain what follows only through the
suffix appended after them. (`PartsFollow` decides token equality through `FollowAt`, so this
keeps `DecidableEq Tok`.) -/
theorem partsFollow_toParts_append (n : Notation Tok G.Ent)
    (suffix : List (Part G)) {s : List Tok} (hsuf : PartsFollow suffix s) :
    PartsFollow (Notation.toParts (G := G) n ++ suffix) s := by
  induction n generalizing suffix with
  | last t =>
      cases suffix with
      | nil => exact trivial
      | cons y r => exact hsuf
  | cons t e' rest ih =>
      obtain ⟨ps, hps⟩ := toParts_head (G := G) rest
      show PartsFollow (Part.namePart t :: Part.hole e' Level.loosest ::
        (Notation.toParts (G := G) rest ++ suffix)) s
      rw [hps]
      have := ih suffix hsuf
      rw [hps] at this
      exact this

/-- **A body constrains its continuation only through a trailing operand hole**, and that hole is
never looser than the operator, so the ambient `FollowAt` tightens onto it. Left-recursive
operators are excluded — they are handled by the spine, not by `udParts`. -/
theorem partsFollow_body {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) (hnl : ((G.entry e).operator o).leftRec = false)
    {s : List Tok} (hs : FollowAt e l s) : PartsFollow (Operator.body e o) s := by
  have htight : FollowAt e (Level.tighter o) s :=
    FollowAt.tighten (condition_up_tighter hc) hs
  have hteq : FollowAt e (Level.tighterEq o) s :=
    FollowAt.tighten (condition_up_tighterEq hc) hs
  cases hop : (G.entry e).operator o with
  | closed n =>
      have hb : Operator.body e o = Notation.toParts (G := G) n ++ [] := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]; exact partsFollow_toParts_append n [] trivial
  | prefx n =>
      have hb : Operator.body e o
          = Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]
      rw [hb]; exact partsFollow_toParts_append n _ htight
  | infx n =>
      have hb : Operator.body e o = Part.hole e (Level.tighter o) ::
          (Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter o)]) := by
        unfold Operator.body; rw [hop]; rfl
      obtain ⟨ps, hps⟩ := toParts_head (G := G) n
      rw [hb, hps]
      have := partsFollow_toParts_append n [Part.hole e (Level.tighter o)] htight
      rw [hps] at this
      exact this
  | infxr n =>
      have hb : Operator.body e o = Part.hole e (Level.tighter o) ::
          (Notation.toParts (G := G) n ++ [Part.hole e (Level.tighterEq o)]) := by
        unfold Operator.body; rw [hop]; rfl
      obtain ⟨ps, hps⟩ := toParts_head (G := G) n
      rw [hb, hps]
      have := partsFollow_toParts_append n [Part.hole e (Level.tighterEq o)] hteq
      rw [hps] at this
      exact this
  | postfx n =>
      have hb : Operator.body e o
          = Part.hole e (Level.tighter o) :: (Notation.toParts (G := G) n ++ []) := by
        unfold Operator.body; rw [hop]; simp
      obtain ⟨ps, hps⟩ := toParts_head (G := G) n
      rw [hb, hps]
      -- `PartsFollow [] s` is `True` for every `s`, so the leftover must be pinned by hand
      have := partsFollow_toParts_append (s := s) n [] trivial
      rw [hps] at this
      exact this
  | infxl n => rw [hop] at hnl; simp [Operator.leftRec] at hnl
  | juxt    => rw [hop] at hnl; simp [Operator.leftRec] at hnl

omit [DecidableEq Tok] in
/-- Both left-recursive fixities lead with a hole, so a token-led operator is not one. -/
theorem Operator.leftRec_of_not_startsWithHole {Ent : Type} {op : Operator Tok Ent}
    (h : op.startsWithHole = false) : op.leftRec = false := by
  cases op <;> simp_all [Operator.startsWithHole, Operator.leftRec]

/-- `partsFollow_body` for a **token-led** operator, which needs only the `.tighter o` half: a
`closed` body ends in a name part and constrains nothing, a `prefx` body in its single operand
hole. Stated over that half alone because the mixed case of `topOp_unique` has exactly it and not
the ambient `FollowAt` it would otherwise be derived from. -/
theorem partsFollow_body_tokenLed {e : G.Ent} {o : (G.entry e).Op}
    (hnh : ((G.entry e).operator o).startsWithHole = false) {s : List Tok}
    (hs : FollowAt e (Level.tighter o) s) : PartsFollow (Operator.body e o) s := by
  cases hop : (G.entry e).operator o with
  | closed n =>
      have hb : Operator.body e o = Notation.toParts (G := G) n ++ [] := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]; exact partsFollow_toParts_append (s := s) n [] trivial
  | prefx n =>
      have hb : Operator.body e o
          = Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]
      rw [hb]; exact partsFollow_toParts_append n _ hs
  | infx n   => rw [hop] at hnh; simp [Operator.startsWithHole] at hnh
  | infxl n  => rw [hop] at hnh; simp [Operator.startsWithHole] at hnh
  | infxr n  => rw [hop] at hnh; simp [Operator.startsWithHole] at hnh
  | postfx n => rw [hop] at hnh; simp [Operator.startsWithHole] at hnh
  | juxt     => rw [hop] at hnh; simp [Operator.startsWithHole] at hnh

/-! ## The left-recursive kernel

`infxl` and `juxt` are the operators `udParts` cannot see: their bodies are not `Seamed`, because
the leading hole sits at `.tighterEq o`, exactly the level at which the operator's own continuation
is applicable. The fix is the spine — but not `Expr.spine`, which would then need an injectivity
proof. Instead the descent carries the tails it has peeled off as an explicit **accumulator**, and
states its conclusion about the *refold*:

    leftRecFold t₁ tails₁ = leftRecFold t₂ tails₂

Peeling one node off `t₁` moves it into `tails₁` and leaves that expression unchanged
(`leftRecFold acc (T :: ts) = leftRecFold (leftRecApp acc T) ts` is the definition), so the goal is
literally invariant under the descent and no reconstruction lemma is needed. When both sides have
descended to a **non-`o`-headed** tree, those are trees at `.tighter o` — where the ★ lemmas do
supply FOLLOW — and the accumulated tail sequences are compared pairwise by `udParts`. -/

omit [DecidableEq Tok] in
/-- A left-recursive body is one node, its leading operand, and its tail. -/
theorem Parts.leftRec_size {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (ps : Parts G (Operator.body e o)) :
    ps.size = 1 + (ps.leftRecL hlr).size + (ps.leftRecT hlr).size := by
  have hb := body_leftRec_cons hlr
  rw [← Parts.size_cast hb ps]
  unfold Parts.leftRecL Parts.leftRecT
  cases (hb ▸ ps : Parts G (.hole e (Level.tighterEq o) :: (Operator.body e o).tail)) with
  | hole L T => rfl

/-- **The refold.** Hang a sequence of body tails off an accumulator, leftmost first — the inverse
of the spine descent, and the invariant the kernel is stated over. -/
def Expr.leftRecFold {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) :
    Expr G e (Level.tighterEq o) → List (Parts G (Operator.body e o).tail) →
      Expr G e (Level.tighterEq o)
  | acc, []      => acc
  | acc, T :: ts => Expr.leftRecFold hlr (Expr.leftRecApp hlr acc T) ts

/-- The size of a tail sequence — the accumulator's share of the induction measure. -/
def tailsSize {shape : List (Part G)} (ts : List (Parts G shape)) : Nat :=
  (ts.map Parts.size).sum

omit [DecidableEq Tok] in
@[simp] theorem tailsSize_nil {shape : List (Part G)} :
    tailsSize ([] : List (Parts G shape)) = 0 := rfl

omit [DecidableEq Tok] in
@[simp] theorem tailsSize_cons {shape : List (Part G)} (T : Parts G shape)
    (ts : List (Parts G shape)) : tailsSize (T :: ts) = T.size + tailsSize ts := rfl

/-- **The level-free content of a tree**: its top operator with its body, or its variable token.
The level index and the applicability proof carry no data, so two trees at *one* level are equal as
soon as this is (`Expr.eq_of_decomp`) — which is what lets a tree be re-levelled from
`.tighterEq o` down to `.tighter o` when its top operator is not `o`, compared there, and the
verdict carried back. -/
def Expr.decomp {e : G.Ent} {l : Level (G.entry e)} :
    Expr G e l → (Σ o : (G.entry e).Op, Parts G (Operator.body e o)) ⊕ Tok
  | .op o _ ps => .inl ⟨o, ps⟩
  | .var t _   => .inr t

omit [DecidableEq Tok] in
/-- Equal content at one level means equal trees: the two proof fields are `Prop`s. -/
theorem Expr.eq_of_decomp {e : G.Ent} {l : Level (G.entry e)} (t₁ t₂ : Expr G e l)
    (h : t₁.decomp = t₂.decomp) : t₁ = t₂ := by
  cases t₁ with
  | op o₁ c₁ ps₁ =>
      cases t₂ with
      | op o₂ c₂ ps₂ =>
          simp only [Expr.decomp, Sum.inl.injEq, Sigma.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
      | var b hb => simp [Expr.decomp] at h
  | var a ha =>
      cases t₂ with
      | op o₂ c₂ ps₂ => simp [Expr.decomp] at h
      | var b hb =>
          simp only [Expr.decomp, Sum.inr.injEq] at h
          subst h; rfl

omit [DecidableEq Tok] in
/-- One step of the descent: an `o`-headed tree at `.tighterEq o` *is* a `leftRecApp`. -/
theorem leftRec_step {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true)
    (c : Level.condition (Level.tighterEq o) o) (ps : Parts G (Operator.body e o)) :
    ∃ (L : Expr G e (Level.tighterEq o)) (T : Parts G (Operator.body e o).tail),
      Expr.op (l := Level.tighterEq o) o c ps = Expr.leftRecApp hlr L T ∧
      (Expr.op (l := Level.tighterEq o) o c ps).flatten = L.flatten ++ T.flatten ∧
      (Expr.op (l := Level.tighterEq o) o c ps).size = 2 + L.size + T.size := by
  refine ⟨ps.leftRecL hlr, ps.leftRecT hlr, ?_, ?_, ?_⟩
  · refine Expr.eq_of_decomp _ _ ?_
    simp only [Expr.leftRecApp, Expr.decomp]
    rw [← Parts.leftRec_eta hlr ps]
  · rw [Expr.flatten, Parts.leftRec_flatten hlr ps]
  · rw [Expr.size, Parts.leftRec_size hlr ps]; omega

omit [DecidableEq Tok] in
/-- **The dichotomy the descent runs on.** A tree at `.tighterEq o` either is `o`-headed — one
`leftRecApp` step onto a strictly smaller tree — or already lives at `.tighter o`, where the ★
lemmas apply (`TighterEq` minus reflexivity is `Tighter`; a `var` inhabits every level). -/
theorem leftRec_view {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (t : Expr G e (Level.tighterEq o)) :
    (∃ (L : Expr G e (Level.tighterEq o)) (T : Parts G (Operator.body e o).tail),
        t = Expr.leftRecApp hlr L T ∧ t.flatten = L.flatten ++ T.flatten ∧
          t.size = 2 + L.size + T.size)
    ∨ (∃ b : Expr G e (Level.tighter o),
        b.decomp = t.decomp ∧ b.flatten = t.flatten ∧ b.size = t.size) := by
  cases t with
  | var a ha => exact Or.inr ⟨Expr.var a ha, rfl, rfl, rfl⟩
  | op o' c ps =>
      by_cases h : o' = o
      · subst h; exact Or.inl (leftRec_step hlr c ps)
      · have hc : Level.condition (Level.tighter o) o' := by
          rcases TighterEq.toTighterOrEq c with heq | hT
          · exact absurd heq.symm h
          · exact hT
        exact Or.inr ⟨Expr.op o' hc ps, rfl, rfl, rfl⟩

omit [DecidableEq Tok] in
/-- `leftRecApp` is injective on the components a body splits into — the inversion that turns the
kernel's spine equality back into an equality of bodies. -/
theorem Parts.eq_of_leftRecApp {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (p₁ p₂ : Parts G (Operator.body e o))
    (h : Expr.leftRecApp hlr (p₁.leftRecL hlr) (p₁.leftRecT hlr)
       = Expr.leftRecApp hlr (p₂.leftRecL hlr) (p₂.leftRecT hlr)) : p₁ = p₂ := by
  have hd := congrArg Expr.decomp h
  simp only [Expr.leftRecApp, Expr.decomp, Sum.inl.injEq, Sigma.mk.injEq, heq_eq_eq,
    true_and] at hd
  rw [Parts.leftRec_eta hlr p₁, Parts.leftRec_eta hlr p₂, hd]

/-- ★★ **The head token of a body tail**, and the two facts the whole kernel runs on. For `infxl`
it is the operator's own head token; for `juxt`, the first token of the right operand, which starts
an operand. Either way it does **not** continue at `.tighter o` (the two ★ lemmas — this is what
bounds the base) but **does** continue at `.tighterEq o`, where `o` is applicable by reflexivity —
and that is what forbids one spine from running out before the other. -/
theorem leftRec_tail_head {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) (T : Parts G (Operator.body e o).tail) :
    ∃ x r, T.flatten = x :: r ∧ ¬ ContinuesAt e (Level.tighter o) x ∧
      ContinuesAt e (Level.tighterEq o) x := by
  cases hop : (G.entry e).operator o with
  | infxl n =>
      have hh : ((G.entry e).operator o).startsWithHole = true := by rw [hop]; rfl
      have hhead : ((G.entry e).operator o).headTok? = some n.firstTok := by
        rw [hop]; simp [Operator.headTok?, Operator.nameTokens, Notation.head?_toTokens]
      have hb : (Operator.body e o).tail = Part.namePart n.firstTok ::
          ((Notation.toParts (G := G) n).tail ++ [Part.hole e (Level.tighter o)]) := by
        unfold Operator.body; rw [hop]; simp [Notation.toParts_append_cons]
      obtain ⟨r, hr⟩ := Parts.flatten_cons_namePart (hb ▸ T)
      exact ⟨n.firstTok, r, by rw [← Parts.flatten_cast hb T, hr],
        not_continuesAt_tighter_head hh hhead, Or.inl ⟨o, TighterEq.refl, hh, hhead⟩⟩
  | juxt =>
      have hb : (Operator.body e o).tail = [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; rfl
      cases hq : (hb ▸ T : Parts G [Part.hole e (Level.tighter o)]) with
      | hole sub tl =>
          obtain ⟨x, r, hxr, hstart⟩ := Expr.flatten_head sub
          refine ⟨x, r ++ tl.flatten, ?_, not_continuesAt_tighter_juxt hop hstart,
            Or.inr ⟨o, TighterEq.refl, hop, hstart⟩⟩
          rw [← Parts.flatten_cast hb T, hq, Parts.flatten, hxr]; simp
  | closed n => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | prefx n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infx n   => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infxr n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | postfx n => rw [hop] at hlr; simp [Operator.leftRec] at hlr

/-- **A tail sequence, then a stopping leftover, stops the base's level.** Either a tail follows —
and its head token does not continue at `.tighter o` — or the leftover does, and stopping
`.tighterEq o` stops `.tighter o`. This is the FOLLOW that the base comparison needs and that the
`.tighterEq o` level cannot give. -/
theorem tails_followAt_tighter {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true)
    (tails : List (Parts G (Operator.body e o).tail)) {s : List Tok}
    (hs : FollowAt e (Level.tighterEq o) s) :
    FollowAt e (Level.tighter o) ((tails.map Parts.flatten).flatten ++ s) := by
  cases tails with
  | nil => simpa using FollowAt.tighter_of_tighterEq hs
  | cons T ts =>
      obtain ⟨x, r, hT, hnc, -⟩ := leftRec_tail_head hlr T
      intro t ht
      simp only [List.map_cons, List.flatten_cons, hT, List.cons_append, List.head?_cons,
        Option.some.injEq] at ht
      subst ht; exact hnc

/-- A body tail ends in the right operand's hole, at `.tighter o` — so that is all it constrains
about what follows it. -/
theorem partsFollow_body_tail {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) {s : List Tok}
    (hs : FollowAt e (Level.tighter o) s) : PartsFollow (Operator.body e o).tail s := by
  cases hop : (G.entry e).operator o with
  | infxl n =>
      have hb : (Operator.body e o).tail
          = Notation.toParts (G := G) n ++ [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; simp
      rw [hb]; exact partsFollow_toParts_append n _ hs
  | juxt =>
      have hb : (Operator.body e o).tail = [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; rfl
      rw [hb]; exact hs
  | closed n => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | prefx n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infx n   => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infxr n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | postfx n => rw [hop] at hlr; simp [Operator.leftRec] at hlr

/-- A left-recursive body tail **is** seamed, unlike the body it came from: the offending leading
`.tighterEq` hole is exactly what `.tail` drops. `seamed_body_tail` for `infxl`; for `juxt` the
tail is a single part, which is seamed vacuously. -/
theorem seamed_body_tail_leftRec {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) : Seamed (Operator.body e o).tail := by
  cases hop : (G.entry e).operator o with
  | infxl n => exact seamed_body_tail (by rw [hop]; rfl)
  | juxt =>
      have hb : (Operator.body e o).tail = [Part.hole e (Level.tighter o)] := by
        unfold Operator.body; rw [hop]; rfl
      rw [hb]; exact trivial
  | closed n => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | prefx n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infx n   => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | infxr n  => rw [hop] at hlr; simp [Operator.leftRec] at hlr
  | postfx n => rw [hop] at hlr; simp [Operator.leftRec] at hlr

/-- **Two tail sequences that print alike are equal.** Pairwise comparison is `udParts` on
`(Operator.body e o).tail`; a sequence that runs out first leaves the *other's* head token in its
leftover, and that token continues at `.tighterEq o` — which the leftover stops. That is the step
that forces equal lengths, and the only one that uses the ambient level. -/
theorem udTails {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) {m : Nat}
    (ihP : ∀ (q₁ q₂ : Parts G (Operator.body e o).tail) (r₁ r₂ : List Tok),
        q₁.size + q₂.size ≤ m → q₁.flatten ++ r₁ = q₂.flatten ++ r₂ →
        PartsFollow (Operator.body e o).tail r₁ → PartsFollow (Operator.body e o).tail r₂ →
        q₁ = q₂ ∧ r₁ = r₂) :
    ∀ (tails₁ tails₂ : List (Parts G (Operator.body e o).tail)) (s₁ s₂ : List Tok),
      tailsSize tails₁ + tailsSize tails₂ ≤ m →
      (tails₁.map Parts.flatten).flatten ++ s₁ = (tails₂.map Parts.flatten).flatten ++ s₂ →
      FollowAt e (Level.tighterEq o) s₁ → FollowAt e (Level.tighterEq o) s₂ →
      tails₁ = tails₂ ∧ s₁ = s₂ := by
  intro tails₁
  induction tails₁ with
  | nil =>
      intro tails₂ s₁ s₂ _ heq hs₁ hs₂
      cases tails₂ with
      | nil => exact ⟨rfl, by simpa using heq⟩
      | cons T ts =>
          exfalso
          obtain ⟨x, r, hT, -, hcont⟩ := leftRec_tail_head hlr T
          refine hs₁ x ?_ hcont
          simp only [List.map_nil, List.flatten_nil, List.nil_append] at heq
          rw [heq]; simp [hT]
  | cons T₁ ts ih =>
      intro tails₂ s₁ s₂ hsz heq hs₁ hs₂
      cases tails₂ with
      | nil =>
          exfalso
          obtain ⟨x, r, hT, -, hcont⟩ := leftRec_tail_head hlr T₁
          refine hs₂ x ?_ hcont
          simp only [List.map_nil, List.flatten_nil, List.nil_append] at heq
          rw [← heq]; simp [hT]
      | cons T₂ ts₂ =>
          have heq' : T₁.flatten ++ ((ts.map Parts.flatten).flatten ++ s₁)
              = T₂.flatten ++ ((ts₂.map Parts.flatten).flatten ++ s₂) := by
            simpa only [List.map_cons, List.flatten_cons, List.append_assoc] using heq
          obtain ⟨hT, hrest⟩ := ihP T₁ T₂ _ _ (by simp only [tailsSize_cons] at hsz; omega) heq'
            (partsFollow_body_tail hlr (tails_followAt_tighter hlr ts hs₁))
            (partsFollow_body_tail hlr (tails_followAt_tighter hlr ts₂ hs₂))
          obtain ⟨hts, hss⟩ := ih ts₂ s₁ s₂ (by simp only [tailsSize_cons] at hsz; omega)
            hrest hs₁ hs₂
          exact ⟨by rw [hT, hts], hss⟩

/-- **The left-recursive kernel.** Two `.tighterEq o` trees carrying tail accumulators, whose
printings agree up to leftovers that stop `.tighterEq o`, refold to the same tree.

The descent peels `o`-headed nodes off either side into its accumulator — which leaves the refold
invariant, so no reconstruction is needed — until both sides are non-`o`-headed. Those are trees at
`.tighter o`, so `udExpr` applies there (`tails_followAt_tighter` is the FOLLOW), and the two tail
sequences are then compared by `udTails`. The two induction hypotheses are passed in rather than
taken from the mutual block, which keeps this recursion independent of that one. -/
theorem leftRecUd (k : Nat) {e : G.Ent} {o : (G.entry e).Op}
    (hlr : ((G.entry e).operator o).leftRec = true) {m : Nat}
    (ihE : ∀ (u₁ u₂ : Expr G e (Level.tighter o)) (r₁ r₂ : List Tok),
        u₁.size + u₂.size ≤ m → u₁.flatten ++ r₁ = u₂.flatten ++ r₂ →
        FollowAt e (Level.tighter o) r₁ → FollowAt e (Level.tighter o) r₂ → u₁ = u₂ ∧ r₁ = r₂)
    (ihP : ∀ (q₁ q₂ : Parts G (Operator.body e o).tail) (r₁ r₂ : List Tok),
        q₁.size + q₂.size ≤ m → q₁.flatten ++ r₁ = q₂.flatten ++ r₂ →
        PartsFollow (Operator.body e o).tail r₁ → PartsFollow (Operator.body e o).tail r₂ →
        q₁ = q₂ ∧ r₁ = r₂)
    (t₁ t₂ : Expr G e (Level.tighterEq o))
    (tails₁ tails₂ : List (Parts G (Operator.body e o).tail)) (s₁ s₂ : List Tok)
    (hk : t₁.size + tailsSize tails₁ + (t₂.size + tailsSize tails₂) ≤ k)
    (hm : t₁.size + tailsSize tails₁ + (t₂.size + tailsSize tails₂) ≤ m)
    (heq : t₁.flatten ++ ((tails₁.map Parts.flatten).flatten ++ s₁)
         = t₂.flatten ++ ((tails₂.map Parts.flatten).flatten ++ s₂))
    (hs₁ : FollowAt e (Level.tighterEq o) s₁) (hs₂ : FollowAt e (Level.tighterEq o) s₂) :
    Expr.leftRecFold hlr t₁ tails₁ = Expr.leftRecFold hlr t₂ tails₂ ∧ s₁ = s₂ := by
  rcases leftRec_view hlr t₁ with ⟨L₁, T₁, he₁, hf₁, hz₁⟩ | ⟨b₁, hd₁, hbf₁, hbz₁⟩
  · -- peel one node off the left
    have hdec : L₁.size + tailsSize (T₁ :: tails₁) + (t₂.size + tailsSize tails₂) < k := by
      simp only [tailsSize_cons]; omega
    have hrec := leftRecUd (L₁.size + tailsSize (T₁ :: tails₁) + (t₂.size + tailsSize tails₂))
      hlr ihE ihP L₁ t₂ (T₁ :: tails₁) tails₂ s₁ s₂ (Nat.le_refl _)
      (by simp only [tailsSize_cons] at *; omega)
      (by rw [hf₁] at heq; simpa only [List.map_cons, List.flatten_cons, ← List.append_assoc]
            using heq)
      hs₁ hs₂
    rw [he₁]
    exact hrec
  · rcases leftRec_view hlr t₂ with ⟨L₂, T₂, he₂, hf₂, hz₂⟩ | ⟨b₂, hd₂, hbf₂, hbz₂⟩
    · -- peel one node off the right
      have hdec : t₁.size + tailsSize tails₁ + (L₂.size + tailsSize (T₂ :: tails₂)) < k := by
        simp only [tailsSize_cons]; omega
      have hrec := leftRecUd (t₁.size + tailsSize tails₁ + (L₂.size + tailsSize (T₂ :: tails₂)))
        hlr ihE ihP t₁ L₂ tails₁ (T₂ :: tails₂) s₁ s₂ (Nat.le_refl _)
        (by simp only [tailsSize_cons] at *; omega)
        (by rw [hf₂] at heq; simpa only [List.map_cons, List.flatten_cons, ← List.append_assoc]
              using heq)
        hs₁ hs₂
      rw [he₂]
      exact hrec
    · -- both sides are bases: compare them at `.tighter o`, then the accumulators
      obtain ⟨hb, hrest⟩ := ihE b₁ b₂ _ _ (by omega) (by rw [hbf₁, hbf₂]; exact heq)
        (tails_followAt_tighter hlr tails₁ hs₁) (tails_followAt_tighter hlr tails₂ hs₂)
      have ht : t₁ = t₂ := Expr.eq_of_decomp t₁ t₂ (by rw [← hd₁, ← hd₂, hb])
      obtain ⟨hts, hss⟩ := udTails hlr ihP tails₁ tails₂ s₁ s₂ (by omega) hrest hs₁ hs₂
      exact ⟨by rw [ht, hts], hss⟩
  termination_by k
  decreasing_by all_goals omega

/-! ## Distinct top operators

`topOp_unique` splits three ways on which of the two competing operators lead with a hole. Two of
the three are closed here; like `leftRecUd`, the mixed case needs `udParts` and so takes it as a
hypothesis rather than living in the mutual block. -/

/-- **The mixed case: one operator hole-led, the other token-led.** ✅ *Closed.*

The hole-led tree's leftmost descent (`op_split_left`) bottoms out either at a **variable** — then
the shared first token is both a variable and the token-led operator's name part, which
`varDisjoint` forbids — or at a **token-led node**, whose head token is that same first token, so
`headsDistinct` makes it the very operator the competing tree is headed by. Two bodies over one
shape: `udParts` identifies them *and their leftovers*. But the hole-led tree had a token left over
after that body — the one `op_split_left` names, which continues at `l` — and it now heads `s₂`,
which `FollowAt e l s₂` forbids.

The FOLLOW `udParts` needs on the hole-led side is exactly `op_split_left`'s third component: that
token cannot continue *below* the bottom operator. Nothing here needs `o₁ ≠ o₂` — a hole-led and a
token-led operator are distinct anyway. -/
theorem topOp_unique_mixed {m : Nat}
    (ihP : ∀ {shape : List (Part G)} (q₁ q₂ : Parts G shape) (r₁ r₂ : List Tok),
        q₁.size + q₂.size ≤ m → q₁.flatten ++ r₁ = q₂.flatten ++ r₂ →
        Seamed shape → PartsFollow shape r₁ → PartsFollow shape r₂ → q₁ = q₂ ∧ r₁ = r₂)
    {e : G.Ent} {l : Level (G.entry e)} {o₁ o₂ : (G.entry e).Op}
    (hc₁ : Level.condition l o₁) (hc₂ : Level.condition l o₂)
    (hh₁ : ((G.entry e).operator o₁).startsWithHole = true)
    (hnh₂ : ((G.entry e).operator o₂).startsWithHole = false)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List (Tok)) (hbound : p₁.size + p₂.size ≤ m)
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₂ : FollowAt e l s₂) : False := by
  obtain ⟨tk₂, r₂, hpf₂, hhead₂⟩ := Parts.flatten_tokenLed hnh₂ p₂
  obtain ⟨x, w, hcont, hbot⟩ := op_split_left hc₁ hh₁ p₁
  rcases hbot with ⟨u, q, hnhu, hstopu, hszu, hfu⟩ | ⟨t, hv, hfu⟩
  · -- the bottom node and `p₂` are token-led and share a first token, so they share an operator
    obtain ⟨tk, r, hqf, hheadu⟩ := Parts.flatten_tokenLed hnhu q
    have htk : tk = tk₂ := by
      rw [hfu, hqf, hpf₂] at heq; simpa using congrArg List.head? heq
    have hu : u = o₂ := head_inj hheadu (htk ▸ hhead₂)
    subst hu
    have hnl : ((G.entry e).operator u).leftRec = false :=
      Operator.leftRec_of_not_startsWithHole hnh₂
    have heq' : q.flatten ++ (x :: w ++ s₁) = p₂.flatten ++ s₂ := by
      rw [hfu] at heq; simpa only [List.append_assoc, List.cons_append] using heq
    obtain ⟨-, hlft⟩ := ihP q p₂ _ _ (by omega) heq' (seamed_body u hnl)
      (partsFollow_body_tokenLed hnh₂ (by
        intro y hy hcy
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hy
        exact hstopu (hy ▸ hcy)))
      (partsFollow_body hc₂ hnl hs₂)
    -- the hole-led tree ran on past that body, and what it ran on with continues at `l`
    exact hs₂ x (by rw [← hlft]; rfl) hcont
  · -- the bottom node is a variable, which cannot be `o₂`'s leading name part
    rw [hfu, hpf₂] at heq
    have : t = tk₂ := by simpa using congrArg List.head? heq
    rw [this, (G.entry e).varDisjoint o₂ tk₂ (Operator.headTok?_mem _ hhead₂)] at hv
    exact Bool.noConfusion hv

/-- **The last gap: two distinct operators, both leading with a hole.**

Why neither closed case reaches it. Against a *token-led* competitor there is a token that pins the
comparison — `topOp_unique_mixed` finds the hole-led tree's leftmost token-led node and matches it
against the competitor outright. Here both flattenings begin with a token that merely *starts an
operand* (a hole-led operator inherits one from its leading operand, `Expr.flatten_head`), and
neither leading operand's extent is bounded by the other's.

What the argument needs, and what `leftRecUd` supplies only for a **fixed** `o`, is the left-spine
decomposition for **all** hole-led operators at once: a tree at `l` is a leftmost operand followed
by a chain of extensions, each applicable at `l`. Uniqueness would then be: the bases agree by
`udParts` (`op_split_left` already produces them, with the FOLLOW), the extensions agree one at a
time by `headsDistinct` on the token each begins with (`juxtUnique` and
`not_startsOperand_of_head` separating juxtaposition from the rest), and a chain that runs out
first leaves the other's next head token in its leftover, which continues at `l`. The obstacle is
not the argument but its *type*: the chain is dependent — each extension's leading hole must admit
the accumulator's top operator — so it is not the plain `List` that `Expr.leftRecFold` gets to use
for a single operator. -/
theorem topOp_unique_bothHoleLed {e : G.Ent} {l : Level (G.entry e)} {o₁ o₂ : (G.entry e).Op}
    (hne : o₁ ≠ o₂) (hc₁ : Level.condition l o₁) (hc₂ : Level.condition l o₂)
    (hh₁ : ((G.entry e).operator o₁).startsWithHole = true)
    (hh₂ : ((G.entry e).operator o₂).startsWithHole = true)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List (Tok))
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : False := by
  sorry

/-- **Two distinct top operators cannot share a flattening.** Token-led/token-led is
`headsDistinct` outright, the mixed case is `topOp_unique_mixed`, and hole-led/hole-led is the one
remaining gap. -/
theorem topOp_unique {m : Nat}
    (ihP : ∀ {shape : List (Part G)} (q₁ q₂ : Parts G shape) (r₁ r₂ : List Tok),
        q₁.size + q₂.size ≤ m → q₁.flatten ++ r₁ = q₂.flatten ++ r₂ →
        Seamed shape → PartsFollow shape r₁ → PartsFollow shape r₂ → q₁ = q₂ ∧ r₁ = r₂)
    {e : G.Ent} {l : Level (G.entry e)} {o₁ o₂ : (G.entry e).Op}
    (hne : o₁ ≠ o₂) (hc₁ : Level.condition l o₁) (hc₂ : Level.condition l o₂)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List (Tok)) (hbound : p₁.size + p₂.size ≤ m)
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : False := by
  cases hnh₁ : ((G.entry e).operator o₁).startsWithHole with
  | true =>
      cases hnh₂ : ((G.entry e).operator o₂).startsWithHole with
      | true => exact topOp_unique_bothHoleLed hne hc₁ hc₂ hnh₁ hnh₂ p₁ p₂ s₁ s₂ heq hs₁ hs₂
      | false => exact topOp_unique_mixed ihP hc₁ hc₂ hnh₁ hnh₂ p₁ p₂ s₁ s₂ hbound heq hs₂
  | false =>
      cases hnh₂ : ((G.entry e).operator o₂).startsWithHole with
      | true =>
          exact topOp_unique_mixed ihP hc₂ hc₁ hnh₂ hnh₁ p₂ p₁ s₂ s₁ (by omega) heq.symm hs₁
      | false => exact topOp_unique_tokenLed hne hnh₁ hnh₂ p₁ p₂ s₁ s₂ heq

/-! ## The mutual unique decomposition

`udExpr` and `udParts` are now genuinely mutually recursive, on summed sizes: an operator node
hands its body to `udParts`, and each hole in a body hands its subtree back to `udExpr`.

`udParts` takes `Seamed`/`PartsFollow` rather than an ambient `FollowAt`, because that is what a
*shape* can actually supply. A shape constrains what follows it only through a trailing hole
(`PartsFollow`) and constrains its interior only at the seams (`Seamed`) — and both are exactly
what the hole case needs to call `udExpr` at the hole's own level. This is why the ancestor's
`splitLeftRec` carried `hb : Operator.body e o = shape`: not to use the equation, but to know the
shape came from a body at all. `Seamed`/`PartsFollow` replace that, and say it locally. -/

/-! ⚠ **Both functions carry an explicit size bound `n` and recurse on it.** The natural measure
`t₁.size + t₂.size` does not work: a `termination_by` measure is stated in terms of the function's
*parameters*, and neither `match` nor `cases` refines it, so in the operator branch the decrease
goal still reads `… < t₁.size + t₂.size` with `t₁` an opaque variable. A bound passed as an
ordinary hypothesis *is* refined by `cases`, so the arithmetic becomes visible. `udExpr`/`udParts`
below re-expose the natural statements. -/

mutual
  /-- Two expressions at the same level whose flattenings agree up to leftovers that **stop** the
  level are equal, with equal leftovers. -/
  theorem udExprN (n : Nat) (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l)
      (s₁ s₂ : List (Tok)) (hn : t₁.size + t₂.size ≤ n)
      (heq : t₁.flatten ++ s₁ = t₂.flatten ++ s₂)
      (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
    cases t₁ with
    | var a ha =>
        cases t₂ with
        | var b hb =>
            simp only [Expr.flatten, List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, hs⟩ := heq
            exact ⟨rfl, hs⟩
        | op o c p =>
            exact absurd heq (fun h => (varOp_ne ha c p s₁ s₂ (by simpa [Expr.flatten] using h)
              hs₁ hs₂).elim)
    | op o₁ c₁ p₁ =>
        cases t₂ with
        | var b hb =>
            exact absurd heq (fun h => (varOp_ne hb c₁ p₁ s₂ s₁
              (by simpa [Expr.flatten] using h.symm) hs₂ hs₁).elim)
        | op o₂ c₂ p₂ =>
            simp only [Expr.size] at hn
            rcases Classical.em (o₁ = o₂) with ho | ho
            -- ⚠ deliberately NOT substituted: substituting `o₂ := o₁` retypes `p₂`, and the size
            -- bound then mentions a different copy. Transport instead; `Parts.size_opCast` and
            -- `Parts.flatten_opCast` say the transport changes neither size nor flattening.
            · cases hlr : ((G.entry e).operator o₁).leftRec with
              | false =>
                  have hsz : (ho.symm ▸ p₂ : Parts G (Operator.body e o₁)).size = p₂.size :=
                    Parts.size_opCast ho.symm p₂
                  have hpe : p₁.flatten ++ s₁
                      = (ho.symm ▸ p₂ : Parts G (Operator.body e o₁)).flatten ++ s₂ := by
                    rw [Parts.flatten_opCast ho.symm p₂]
                    simpa only [Expr.flatten] using heq
                  obtain ⟨hp, hss⟩ := udPartsN (p₁.size + p₂.size) p₁ (ho.symm ▸ p₂) s₁ s₂
                    (by omega) (seamed_body o₁ hlr)
                    (partsFollow_body c₁ hlr hs₁) (partsFollow_body c₁ hlr hs₂) hpe
                  subst ho
                  exact ⟨by rw [hp], hss⟩
              | true =>
                  -- `infxl`/`juxt`: the body is NOT `Seamed` — its leading hole is at
                  -- `.tighterEq o₁`, where the operator's own head token (and, for `juxt`, an
                  -- operand-starter) *does* continue, so neither ★ lemma bounds it and `udParts`
                  -- does not apply. Hand the two bodies to `leftRecUd` as one-tail spines
                  -- instead: it peels the chain down to two bases at `.tighter o₁`, where FOLLOW
                  -- is available again, and compares the accumulated tails with `udParts` on
                  -- `(Operator.body e o₁).tail` (which IS seamed).
                  have hsz : (ho.symm ▸ p₂ : Parts G (Operator.body e o₁)).size = p₂.size :=
                    Parts.size_opCast ho.symm p₂
                  have hpe : p₁.flatten ++ s₁
                      = (ho.symm ▸ p₂ : Parts G (Operator.body e o₁)).flatten ++ s₂ := by
                    rw [Parts.flatten_opCast ho.symm p₂]
                    simpa only [Expr.flatten] using heq
                  have hz₁ := Parts.leftRec_size hlr p₁
                  have hz₂ := Parts.leftRec_size hlr (ho.symm ▸ p₂ : Parts G (Operator.body e o₁))
                  obtain ⟨hfold, hss⟩ := leftRecUd _ hlr (m := p₁.size + p₂.size)
                    (fun u₁ u₂ r₁ r₂ hb hf f₁ f₂ =>
                      udExprN (p₁.size + p₂.size) e (Level.tighter o₁) u₁ u₂ r₁ r₂ hb hf f₁ f₂)
                    (fun q₁ q₂ r₁ r₂ hb hf f₁ f₂ =>
                      udPartsN (p₁.size + p₂.size) q₁ q₂ r₁ r₂ hb
                        (seamed_body_tail_leftRec hlr) f₁ f₂ hf)
                    (p₁.leftRecL hlr)
                    ((ho.symm ▸ p₂ : Parts G (Operator.body e o₁)).leftRecL hlr)
                    [p₁.leftRecT hlr]
                    [(ho.symm ▸ p₂ : Parts G (Operator.body e o₁)).leftRecT hlr] s₁ s₂
                    (Nat.le_refl _)
                    (by simp only [tailsSize_cons, tailsSize_nil]; omega)
                    (by rw [Parts.leftRec_flatten hlr p₁,
                          Parts.leftRec_flatten hlr (ho.symm ▸ p₂ :
                            Parts G (Operator.body e o₁))] at hpe
                        simpa using hpe)
                    (FollowAt.tighten (condition_tighterEq_up c₁) hs₁)
                    (FollowAt.tighten (condition_tighterEq_up c₁) hs₂)
                  have hp : p₁ = (ho.symm ▸ p₂ : Parts G (Operator.body e o₁)) :=
                    Parts.eq_of_leftRecApp hlr _ _ (by simpa [Expr.leftRecFold] using hfold)
                  subst ho
                  exact ⟨by rw [hp], hss⟩
            · exact absurd heq (fun h => (topOp_unique (m := p₁.size + p₂.size)
                (fun q₁ q₂ r₁ r₂ hbb hf hsm f₁ f₂ =>
                  udPartsN (p₁.size + p₂.size) q₁ q₂ r₁ r₂ hbb hsm f₁ f₂ hf)
                ho c₁ c₂ p₁ p₂ s₁ s₂ (Nat.le_refl _)
                (by simpa only [Expr.flatten] using h) hs₁ hs₂).elim)
  termination_by n
  decreasing_by all_goals (simp only [Expr.size] at hn ⊢; omega)

  /-- **Two bodies over one shape agree.** Induction on the shape; the hole case is the call back
  into `udExprN`, at the hole's own entry and level. -/
  theorem udPartsN (n : Nat) {shape : List (Part G)} (p₁ p₂ : Parts G shape) (s₁ s₂ : List (Tok))
      (hn : p₁.size + p₂.size ≤ n)
      (hseam : Seamed shape) (hpf₁ : PartsFollow shape s₁) (hpf₂ : PartsFollow shape s₂)
      (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    cases shape with
    | nil =>
        cases p₁; cases p₂
        exact ⟨rfl, by simpa [Parts.flatten] using heq⟩
    | cons hd tl =>
        -- `PartsFollow` only reduces once `hd` is a constructor, so the tail facts are derived
        -- inside each branch rather than once up front
        cases hd with
        | namePart tk =>
            have hs' : Seamed tl := by
              cases tl with
              | nil => exact trivial
              | cons y r => exact hseam
            have hf₁ : PartsFollow tl s₁ := by
              cases tl with
              | nil => exact trivial
              | cons y r => exact hpf₁
            have hf₂ : PartsFollow tl s₂ := by
              cases tl with
              | nil => exact trivial
              | cons y r => exact hpf₂
            cases p₁ with
            | namePart _ q₁ =>
              cases p₂ with
              | namePart _ q₂ =>
                simp only [Parts.flatten, List.cons_append, List.cons.injEq] at heq
                simp only [Parts.size] at hn
                obtain ⟨hq, hss⟩ := udPartsN (q₁.size + q₂.size) q₁ q₂ s₁ s₂ (by omega)
                  hs' hf₁ hf₂ heq.2
                exact ⟨by rw [hq], hss⟩
        | hole e' L =>
            have hs' : Seamed tl := by
              cases tl with
              | nil => exact trivial
              | cons y r => exact hseam.2
            have hf₁ : PartsFollow tl s₁ := by
              cases tl with
              | nil => exact trivial
              | cons y r => exact hpf₁
            have hf₂ : PartsFollow tl s₂ := by
              cases tl with
              | nil => exact trivial
              | cons y r => exact hpf₂
            cases p₁ with
            | hole sub₁ q₁ =>
              cases p₂ with
              | hole sub₂ q₂ =>
                simp only [Parts.size] at hn
                -- the seam: whatever follows this hole must stop it, **at the hole's own level**
                have hstop : ∀ (q : Parts G tl) (s : List Tok),
                    PartsFollow (Part.hole e' L :: tl) s → FollowAt e' L (q.flatten ++ s) := by
                  intro q s hpf
                  cases tl with
                  | nil =>
                      cases q
                      simpa [Parts.flatten] using hpf
                  | cons y r =>
                      match y, hseam with
                      | .namePart t, ⟨hnc, _⟩ =>
                          cases q with
                          | namePart _ q' =>
                              intro x hx
                              simp only [Parts.flatten, List.cons_append, List.head?_cons,
                                Option.some.injEq] at hx
                              subst hx
                              exact hnc
                have heq' : sub₁.flatten ++ (q₁.flatten ++ s₁)
                    = sub₂.flatten ++ (q₂.flatten ++ s₂) := by
                  simpa only [Parts.flatten, List.append_assoc] using heq
                obtain ⟨hsub, htail⟩ :=
                  udExprN (sub₁.size + sub₂.size) e' L sub₁ sub₂
                    (q₁.flatten ++ s₁) (q₂.flatten ++ s₂) (by omega) heq'
                    (hstop q₁ s₁ hpf₁) (hstop q₂ s₂ hpf₂)
                obtain ⟨hq, hss⟩ := udPartsN (q₁.size + q₂.size) q₁ q₂ s₁ s₂ (by omega)
                  hs' hf₁ hf₂ htail
                exact ⟨by rw [hsub, hq], hss⟩
  termination_by n
  decreasing_by all_goals (simp only [Parts.size] at hn ⊢; omega)
end

/-- Two expressions at one level with stopping leftovers are equal — the natural statement, with
the size bound discharged. -/
theorem udExpr (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l) (s₁ s₂ : List (Tok))
    (heq : t₁.flatten ++ s₁ = t₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : t₁ = t₂ ∧ s₁ = s₂ :=
  udExprN _ e l t₁ t₂ s₁ s₂ (Nat.le_refl _) heq hs₁ hs₂

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
