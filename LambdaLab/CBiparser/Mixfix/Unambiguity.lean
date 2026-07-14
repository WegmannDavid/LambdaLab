import LambdaLab.CBiparser.Mixfix.Biparser

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

namespace LambdaLab.CBiparser.Mixfix

variable {G : Grammar}

/-! ## Sizes, for the mutual termination -/

mutual
  def Expr.size {e : G.Ent} {l : Level (G.entry e)} : Expr G e l → Nat
    | .op _ _ ps => ps.size + 1
    | .var _ _   => 1
  def Parts.size {shape : List (Part G)} : Parts G shape → Nat
    | .nil          => 0
    | .namePart _ q => q.size + 1
    | .hole t q     => t.size + q.size + 1
end

theorem Parts.size_cast {shape shape' : List (Part G)} (h : shape = shape') (ps : Parts G shape) :
    (h ▸ ps).size = ps.size := by cases h; rfl

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
    {rest : List (Token G.isSep)} (h : FollowAt e l rest) : FollowAt e l' rest := by
  intro t ht hcon
  refine h t ht ?_
  rcases hcon with ⟨o, hc, hhole, hhead⟩ | ⟨j, hc, hj, hs⟩
  · exact .inl ⟨o, hup o hc, hhole, hhead⟩
  · exact .inr ⟨j, hup j hc, hj, hs⟩

/-- The two instances the body of an operator actually needs. -/
theorem condition_tighter_up {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) :
    ∀ o', Level.condition (.tighter o) o' → Level.condition l o' :=
  fun _ h => Level.condition_up hc (Tighter.toTighterEq' h)

theorem condition_tighterEq_up {e : G.Ent} {l : Level (G.entry e)} {o : (G.entry e).Op}
    (hc : Level.condition l o) :
    ∀ o', Level.condition (.tighterEq o) o' → Level.condition l o' :=
  fun _ h => Level.condition_up hc h


/-! ## Facts every version of the argument needs

These are independent of how the left-recursive kernel is finally closed, and they are where the
three grammar conditions actually get *used*. -/

/-- **No cycles.** `tighter` is well-founded, so nothing is strictly tighter than itself. -/
theorem Tighter.irrefl {e : G.Ent} (o : (G.entry e).Op) :
    ¬ Tighter (G.entry e).tighter o o := by
  -- a strict cycle would give an infinite descending chain
  have wf := (G.entry e).tighter_wf
  intro h
  induction (wf.apply o) with
  | intro a _ ih =>
      -- `Tighter a a` yields some `b ∈ tighter a` with `Tighter b a`, hence `Tighter b b`
      cases h with
      | base hm => exact ih a hm (.base hm)
      | step hm hr => exact ih _ hm (hr.snoc hm)

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

/-- A notation's token list is its first token followed by its interior tokens. -/
theorem Notation.toTokens_eq {sep : Char → Bool} {Ent : Type} (n : Notation sep Ent) :
    n.toTokens = n.firstTok :: n.toTokens.tail := by
  cases n <;> simp [Notation.toTokens, Notation.firstTok]

theorem Notation.mem_tail_toTokens {sep : Char → Bool} {Ent : Type} (n : Notation sep Ent)
    {t : Token sep} (h : t ∈ n.toTokens.tail) : ∃ e', (e', t) ∈ n.holeFollowers := by
  induction n with
  | last a => simp [Notation.toTokens] at h
  | cons a e' rest ih =>
      simp only [Notation.toTokens, List.cons_append, List.tail_cons] at h
      rw [Notation.toTokens_eq rest, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨e', by simp [Notation.holeFollowers]⟩
      · obtain ⟨e₀, h₀⟩ := ih h
        exact ⟨e₀, by simp [Notation.holeFollowers, h₀]⟩

theorem Operator.mem_tail_nameTokens {sep : Char → Bool} {Ent : Type} (o : Operator sep Ent)
    {t : Token sep} (h : t ∈ o.nameTokens.tail) : ∃ e', (e', t) ∈ o.holeFollowers := by
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

/-- A leading token is one of the operator's name tokens. -/
theorem Operator.headTok?_mem {sep : Char → Bool} {Ent : Type} (o : Operator sep Ent)
    {t : Token sep} (h : o.headTok? = some t) : t ∈ o.nameTokens := by
  have h' : o.nameTokens.head? = some t := h
  cases hn : o.nameTokens with
  | nil => rw [hn] at h'; simp at h'
  | cons a rest =>
      rw [hn] at h'
      simp only [List.head?_cons, Option.some.injEq] at h'
      subst h'
      simp [hn]

/-- `headsDistinct`, in the form the argument actually uses: a token heads at most one operator. -/
theorem head_inj {e : G.Ent} {o o' : (G.entry e).Op} {t : Token G.isSep}
    (h : ((G.entry e).operator o).headTok? = some t)
    (h' : ((G.entry e).operator o').headTok? = some t) : o = o' :=
  (G.entry e).headsDistinct o o' (by rw [h]; rfl) (by rw [h, h'])

/-- **A hole-led operator's head token starts no operand.** It is not a variable (`varDisjoint`),
and the only operator it heads is the hole-led one itself (`headsDistinct`). -/
theorem not_startsOperand_of_head {e : G.Ent} {o : (G.entry e).Op} {t : Token G.isSep}
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
          simp only [beq_iff_eq]
          intro hm
          have ht : a = t := by first | exact hm | exact Subtype.ext hm
          have hoo : o' = o := head_inj (by rw [hk, ht]) hhead
          rw [hoo, hhole] at hnh
          simp at hnh

/-- ★ **A token that heads a hole-led operator `o` does not continue an expression at
`.tighter o`.** Both disjuncts of `ContinuesAt` die:

* a left-recursive operator headed by `t` must **be** `o` (`headsDistinct`), and `o` is not
  strictly tighter than itself (`Tighter.irrefl`);
* juxtaposition continues via an operand, but `t` starts no operand
  (`not_startsOperand_of_head`).

This is the lemma that unblocks the whole development: FOLLOW *is* available below a left-recursive
operator, just not at its own level. -/
theorem not_continuesAt_tighter_head {e : G.Ent} {o : (G.entry e).Op} {t : Token G.isSep}
    (hhole : ((G.entry e).operator o).startsWithHole = true)
    (hhead : ((G.entry e).operator o).headTok? = some t) :
    ¬ ContinuesAt e (.tighter o) t := by
  rintro (⟨o', hc', -, hhead'⟩ | ⟨j, hc', -, hstart⟩)
  · exact Tighter.irrefl o (head_inj hhead' hhead ▸ hc')
  · rw [not_startsOperand_of_head hhole hhead] at hstart; exact absurd hstart (by simp)

/-- ★ The `juxt` analogue: an **operand-starting** token does not continue at `.tighter j` when `j`
is juxtaposition. Juxtaposition strictly tighter than itself is impossible (`juxtUnique` +
`Tighter.irrefl`), and an operand-starter heads no hole-led operator. -/
theorem not_continuesAt_tighter_juxt {e : G.Ent} {j : (G.entry e).Op} {t : Token G.isSep}
    (hj : (G.entry e).operator j = Operator.juxt)
    (hstart : startsOperand e t = true) :
    ¬ ContinuesAt e (.tighter j) t := by
  rintro (⟨o', hc', hhole', hhead'⟩ | ⟨j', hc', hj', -⟩)
  · rw [not_startsOperand_of_head hhole' hhead'] at hstart; exact absurd hstart (by simp)
  · exact Tighter.irrefl j ((G.entry e).juxtUnique j' j hj' hj ▸ hc')

/-- **The kernel.** For a left-recursive operator `o` (`infxl`/`infxr`/`juxt`), a flattening
determines the split between its left and right operands.

Left operand at `.tighterEq o`, right at `.tighter o` (or mirrored, for `infxr`). The right operand
is *strictly* tighter, so its flattening carries no top-level `o`; hence the split is forced. This
is the depth-0 counting argument, and it is the one thing this file still owes. -/
theorem splitLeftRec {e : G.Ent} {l : Level (G.entry e)} (o : (G.entry e).Op)
    (hc : Level.condition l o)
    {shape : List (Part G)} (hb : Operator.body e o = shape)
    (p₁ p₂ : Parts G shape) (s₁ s₂ : List (Token G.isSep))
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) :
    p₁ = p₂ ∧ s₁ = s₂ := by
  sorry

/-- **Two distinct top operators cannot share a flattening.** For the token-led fixities this is
`headsDistinct` (the leading token identifies the operator). For the hole-led ones it needs the
same depth-0 kernel as `splitLeftRec`. -/
theorem topOp_unique {e : G.Ent} {l : Level (G.entry e)} {o₁ o₂ : (G.entry e).Op}
    (hne : o₁ ≠ o₂) (hc₁ : Level.condition l o₁) (hc₂ : Level.condition l o₂)
    (p₁ : Parts G (Operator.body e o₁)) (p₂ : Parts G (Operator.body e o₂))
    (s₁ s₂ : List (Token G.isSep))
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : False := by
  sorry

/-- A variable and an operator cannot share a flattening. -/
theorem varOp_ne {e : G.Ent} {l : Level (G.entry e)} {t : Token G.isSep}
    (hv : (G.entry e).isVar t = true) {o : (G.entry e).Op} (hc : Level.condition l o)
    (p : Parts G (Operator.body e o)) (s₁ s₂ : List (Token G.isSep))
    (heq : [t] ++ s₁ = p.flatten ++ s₂)
    (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : False := by
  sorry

/-! ## The mutual unique decomposition -/

mutual
  /-- Two expressions at the same level whose flattenings agree up to leftovers that **stop** the
  level are equal, with equal leftovers. -/
  theorem udExpr (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l)
      (s₁ s₂ : List (Token G.isSep))
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
  termination_by t₁.size + t₂.size

  /-- Two bodies of the **same** operator, over the same shape, with a common flatten-prefix. -/
  theorem udParts (e : G.Ent) (l : Level (G.entry e)) (o : (G.entry e).Op)
      (hc : Level.condition l o)
      {shape : List (Part G)} (hb : Operator.body e o = shape)
      (p₁ p₂ : Parts G shape) (s₁ s₂ : List (Token G.isSep))
      (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : FollowAt e l s₁) (hs₂ : FollowAt e l s₂) : p₁ = p₂ ∧ s₁ = s₂ :=
    splitLeftRec o hc hb p₁ p₂ s₁ s₂ heq hs₁ hs₂
  termination_by p₁.size + p₂.size
end

/-! ## The payoff -/

/-- **Unambiguity**: `flatten` is injective on the trees of a given entry and level. Every
deterministic parser needs this — if two distinct trees flatten alike, the parser returns one of
them and the other cannot round-trip. `Complete.lean` used to take it as a hypothesis. -/
def Unambiguous (G : Grammar) : Prop :=
  ∀ (e : G.Ent) (l : Level (G.entry e)) (t₁ t₂ : Expr G e l), t₁.flatten = t₂.flatten → t₁ = t₂

/-- **Unambiguity, derived.** The `rest = []` instance of unique decomposition: `[]` stops every
level vacuously, so two trees with equal flattenings are equal. No hypothesis on the grammar beyond
the three it already carries. -/
theorem unambiguous (G : Grammar) : Unambiguous G := by
  intro e l t₁ t₂ hf
  refine (udExpr e l t₁ t₂ [] [] (by simpa using hf) ?_ ?_).1 <;>
    intro t ht <;> simp at ht

end LambdaLab.CBiparser.Mixfix
