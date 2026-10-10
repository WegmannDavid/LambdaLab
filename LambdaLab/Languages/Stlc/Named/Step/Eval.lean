import LambdaLab.Stlc.Named.Typing.Normalization

/-!
# Total normalizer (named variant)

`Term.eval e h` returns the normal form of `e`, given a strong-normalization
proof. `HasType.eval ht` is the convenience wrapper that supplies the SN
proof via `HasType.sn`.

The recursion is on the term: `findReductStep` picks a leftmost-outermost
redex (structural recursion on `Term`); the outer loop iterates that
until the term is in normal form. Termination of the loop is certified
by `SN`, packaged into a `WellFoundedRelation` on `SNTerm` so Lean
compiles via `WellFounded.fix`.
-/

namespace LambdaLab.Stlc.Named

variable {N : Type} [LambdaLab.Nominal.Atom N]

/-- Computable redex picker: leftmost-outermost. Returns `some ⟨e', s⟩`
where `s : Step e e'` if `e` has any redex; `none` if `e` is in
β-normal form. -/
def Term.findReductStep : (e : (Term N)) → Option ((e' : (Term N)) ×' Step e e')
  | .var _                  => none
  | .lam x τ body           =>
      match body.findReductStep with
      | some ⟨body', s⟩ => some ⟨.lam x τ body', Step.lam s⟩
      | none            => none
  | .app (.lam x _ body) v  =>
      some ⟨body.subst x v, Step.beta⟩
  | .app f a                =>
      match f.findReductStep with
      | some ⟨f', s⟩ => some ⟨.app f' a, Step.appL s⟩
      | none =>
          match a.findReductStep with
          | some ⟨a', s⟩ => some ⟨.app f a', Step.appR s⟩
          | none         => none

/-- An SN-witnessed term. The Subtype packages the `SN` proof so we can
attach a `WellFoundedRelation` whose underlying relation is `Step` on
the term components. -/
abbrev SNTerm (N : Type) [LambdaLab.Nominal.Atom N] := { e : (Term N) // SN e }

instance : WellFoundedRelation (SNTerm N) where
  rel := fun a b => Step b.val a.val
  wf := ⟨fun ⟨_, h⟩ => by
    induction h with
    | intro _ ih =>
        constructor
        intro ⟨e', _⟩ hs
        exact ih e' hs⟩

/-- Total evaluator: returns the normal form of `e` given an `SN` proof. -/
def Term.eval (e : (Term N)) (h : SN e) : (Term N) :=
  match e.findReductStep with
  | none         => e
  | some ⟨e', s⟩ => Term.eval e' (h.unfold s)
termination_by (⟨e, h⟩ : SNTerm N)

/-- Any well-typed term has a normal form. The bridge preconditions this used to require are
gone: `HasType.sn` is now unconditional. -/
def HasType.eval {Γ : Ctx N} {e : (Term N)} {τ : Ty}
    (ht : HasType Γ e τ) : (Term N) :=
  Term.eval e (HasType.sn ht)

/-! ## What `eval` returns

Two facts, and neither implies the other: the answer admits no further reduction, and it is
reachable from the input. Together they say `eval` computes a normal form *of `e`*.
-/

/-- **The redex picker is complete**: if a term steps at all, `findReductStep` finds something.

Stated as the contrapositive of what is wanted, because that is the direction the induction goes:
on `Step`, not on the term. Inducting on the term instead would have to reproduce the nested
`.app (.lam ..) _` match by hand in every case. -/
theorem Term.findReductStep_ne_none {e e' : Term N} (s : Step e e') :
    e.findReductStep ≠ none := by
  induction s with
  | beta => simp [Term.findReductStep]
  | lam _ ih =>
      simp only [Term.findReductStep]
      split <;> simp_all
  | @appL e₁ _ _ _ ih =>
      cases e₁ <;> simp only [Term.findReductStep] <;> (repeat' split) <;>
        simp_all [Term.findReductStep]
  | @appR _ _ e₁ _ ih =>
      cases e₁ <;> simp only [Term.findReductStep] <;> (repeat' split) <;> simp_all

/-- **`eval` finishes the job**: nothing reduces its answer. -/
theorem Term.eval_normalForm (e : Term N) (h : SN e) :
    ∀ e', ¬ Step (e.eval h) e' := by
  rw [Term.eval]
  split
  · next hf => exact fun e' s => Term.findReductStep_ne_none s hf
  · next e' s _ => exact Term.eval_normalForm e' (h.unfold s)
termination_by (⟨e, h⟩ : SNTerm N)

/-- **`eval` answers the question asked**: its result is reachable from the input, so it is a
normal form *of `e`* and not merely some normal term. -/
theorem Term.mstep_eval (e : Term N) (h : SN e) : e ⟶* e.eval h := by
  rw [Term.eval]
  split
  · exact RTC.refl
  · next e' s _ => exact RTC.head s (Term.mstep_eval e' (h.unfold s))
termination_by (⟨e, h⟩ : SNTerm N)

/-- **Reduction never invents a metavariable**, all the way to the normal form. `Step.annotsGround`
folded along the reduction sequence `eval` actually takes — which is the form the vernacular needs,
since `HasTypeGround` demands `Ground` of every body it accepts. -/
theorem Term.mstep_annotsGround {e e' : Term N} (h : e ⟶* e') :
    e.AnnotsGround → e'.AnnotsGround := by
  induction h with
  | refl => exact id
  | tail _ s ih => exact fun he => Step.annotsGround s (ih he)

/-- **`eval` returns a ground term when given one.** -/
theorem Term.eval_annotsGround (e : Term N) (h : SN e) (he : e.AnnotsGround) :
    (e.eval h).AnnotsGround :=
  Term.mstep_annotsGround (Term.mstep_eval e h) he

end LambdaLab.Stlc.Named
