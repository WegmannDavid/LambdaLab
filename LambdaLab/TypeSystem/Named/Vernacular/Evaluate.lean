import LambdaLab.TypeSystem.Named.Vernacular.Elaborate

/-!
# Running a program, as a walk

`Elaborate.lean` turns a program into one with no metavariables left; this turns *that* into one
with no work left. Each declaration is reduced in turn, and the result is fully **closed**: the
earlier declarations it mentions have been inlined, and every redex — including the ones inlining
created — is gone.

So this is δ *and* β. The δ half is not decoration: a declared name enters the context as a free
variable, so `λ x . id ( id x )` is already β-normal and β alone would leave almost every program
untouched. Inlining `id` is what turns it into `λ x . x`.

## The state: the declarations already reduced

Left to right, carrying an environment of the declarations already reduced:

    v₁ = eval t₁
    vᵢ = eval (tᵢ[x₁ := v₁] … [xᵢ₋₁ := vᵢ₋₁])

Substituting the *reduced* values rather than the source bodies is what keeps this linear instead
of exponential in the nesting of definitions, and it is also what makes the result closed at every
step: each `vᵢ` is closed because everything it could have mentioned has been replaced by something
closed.

The environment carries proofs, not just values (`EnvEntry`): `tsubst_typing` wants each value
typed, `tsubst_ground` wants it ground, and the context the entries stand for must be ground for
the step below to re-read its typing. They live in the type rather than beside it, where they would
have to be threaded as hypotheses through the step and every theorem about it.

## Where the typing derivation comes from

`HasEval.eval` takes a typing derivation, because that is where strong normalization comes from.
A walk's step is handed a bare declaration, so it obtains the derivation itself: it checks the
declaration with the language's own decision procedure (`PrincipalElaborate.elaborate`) against the
context the environment stands for. On a ground declaration `elaborate` answers with a substitution
that changes nothing, so its typing *is* the declaration's (`typed_of_solution`). A declaration that
does not check is rejected — which, on the output of elaboration, never happens
(`evalWalk_run_isSome`).

## The facts

What the walk produces is well-typed (`evalWalk_sound`), every body closed and normal
(`evalRunFrom_reduced`), and the walk is idempotent a step at a time: handed a declaration it has
already reduced, a step returns it, and records the very same environment entry
(`evalWalk_stepIdempotent`). That is why `Reduced` says *closed* and not merely *normal*: on a closed
body every substitution is a no-op by `tsubst_closed`, so the second pass has nothing to do. A body
that were only normal could still mention an earlier name, and inlining it would change the program
— idempotence would be false.

As the stage after elaboration, it runs on elaborated programs and must keep them elaborated
(`evalWalk_lawfulOn`): it does, because what it produces is well-typed, and well-typed programs are
what elaboration leaves unchanged.
-/

namespace LambdaLab.TypeSystem.Named.Vernacular

open HasVars (Ground)
open LambdaLab.Nominal (Atom)
open LambdaLab.Semantics (Walk)

/-! Only `[Runnable]`, and no bare `[HasType]`, `[LawfulHasEval]` or `[HasTermSubst]` beside it. A
separate instance variable would be a *second*, unrelated judgement: the derivations `elaborate`
produces would not be the ones `eval` and `tsubst` accept, and every application below is a type
error. Same discipline as `Elaborate.lean`, which takes `[PrincipalElaborate]` alone. -/

variable {N Tm Ty : Type} [Atom N] [Runnable N Tm Ty]

/-! ## The environment -/

/-- A declaration already reduced: its value, with the facts every later declaration needs of it.
`typed` in the **empty** context is the closedness that makes inlining idempotent. -/
structure EnvEntry (N Tm Ty : Type) [Atom N] [Runnable N Tm Ty] where
  /-- The name it was declared under. -/
  name : N
  /-- Its declared type. -/
  ty : Ty
  /-- Its reduced body. -/
  value : Tm
  /-- Closed at its declared type. -/
  typed : (Context.empty : Context N Ty) ⊢ value : ty
  /-- Holding no metavariable, which `HasTypeGround` demands of every body. -/
  ground : Ground value
  /-- Nor does its type, so the context the entries stand for is ground. -/
  tyGround : Ground ty

/-- Entries are their data; the proofs come along. -/
theorem EnvEntry.ext {e e' : EnvEntry N Tm Ty} (hn : e.name = e'.name) (ht : e.ty = e'.ty)
    (hv : e.value = e'.value) : e = e' := by
  cases e; cases e'
  simp only at hn ht hv
  subst hn ht hv
  rfl

/-- The declarations reduced so far, **most recent first** — so the head is the outermost `cons` of
the context they stand for, which is the end `tsubst_typing` peels. -/
abbrev Env (N Tm Ty : Type) [Atom N] [Runnable N Tm Ty] := List (EnvEntry N Tm Ty)

/-- The context an environment stands for. -/
def envCtx : Env N Tm Ty → Context N Ty
  | [] => Context.empty
  | e :: ρ => (envCtx ρ).cons e.name e.ty

theorem envCtx_ground : ∀ ρ : Env N Tm Ty, CtxGround (envCtx ρ)
  | [] => CtxGround.empty
  | e :: ρ => (envCtx_ground ρ).cons e.tyGround

/-- **Inline every declaration in the environment**, outermost first. -/
def instantiate : Env N Tm Ty → Tm → Tm
  | [], t => t
  | e :: ρ, t => instantiate ρ (HasTermSubst.tsubst (Ty := Ty) t e.name e.value)

/-- Inlining closes a term: it types in the empty context afterwards. Each step is
`tsubst_typing`, peeling one `cons` off the context. -/
theorem instantiate_typing : ∀ (ρ : Env N Tm Ty) {t : Tm} {τ : Ty},
    envCtx ρ ⊢ t : τ → (Context.empty : Context N Ty) ⊢ instantiate ρ t : τ
  | [], _, _, h => h
  | e :: ρ, _, _, h => instantiate_typing ρ (HasTermSubst.tsubst_typing h e.typed)

/-- Inlining introduces no metavariable. -/
theorem instantiate_ground : ∀ (ρ : Env N Tm Ty) {t : Tm}, Ground t → Ground (instantiate ρ t)
  | [], _, h => h
  | e :: ρ, _, h => instantiate_ground ρ (HasTermSubst.tsubst_ground h e.ground)

/-- **Inlining does nothing to a closed term** — the idempotence half. -/
theorem instantiate_closed : ∀ (ρ : Env N Tm Ty) {t : Tm} {τ : Ty},
    (Context.empty : Context N Ty) ⊢ t : τ → instantiate ρ t = t
  | [], _, _, _ => rfl
  | e :: ρ, _, _, h => by
      rw [instantiate, HasTermSubst.tsubst_closed h e.typed]
      exact instantiate_closed ρ h

/-! ## Reducing one declaration -/

/-- One declaration reduced, packaged as the environment entry the next one will use. -/
def reduce (ρ : Env N Tm Ty) (x : N) (τ : Ty) {t : Tm} (h : envCtx ρ ⊢ t : τ) (hg : Ground t)
    (hτ : Ground τ) : EnvEntry N Tm Ty :=
  { name := x, ty := τ
    value := HasEval.eval Context.empty (instantiate ρ t) τ (instantiate_typing ρ h)
    typed := preservation_mstep (instantiate_typing ρ h)
      (LawfulHasEval.evalReachable (instantiate_typing ρ h))
    ground := LawfulHasEval.evalGround (instantiate_typing ρ h) (instantiate_ground ρ hg)
    tyGround := hτ }

/-- The reduced value admits no further reduction. -/
theorem reduce_normal (ρ : Env N Tm Ty) (x : N) (τ : Ty) {t : Tm} (h : envCtx ρ ⊢ t : τ)
    (hg : Ground t) (hτ : Ground τ) : NormalForm (reduce ρ x τ h hg hτ).value :=
  LawfulHasEval.evalNormal (instantiate_typing ρ h)

/-- **Reducing a body that is already closed and normal returns it.** Inlining is a no-op on it
(`instantiate_closed`) and so is evaluation (`eval_of_normalForm`). -/
theorem reduce_value_of_reduced (ρ : Env N Tm Ty) (x : N) (τ : Ty) {t : Tm}
    (h : envCtx ρ ⊢ t : τ) (hg : Ground t) (hτ : Ground τ)
    (hc : (Context.empty : Context N Ty) ⊢ t : τ) (hn : NormalForm t) :
    (reduce ρ x τ h hg hτ).value = t := by
  show HasEval.eval Context.empty (instantiate ρ t) τ (instantiate_typing ρ h) = t
  -- The derivation mentions `instantiate ρ t` too, so `rw` cannot move the term alone;
  -- `eval_congr` moves both at once.
  rw [eval_congr (instantiate_closed ρ hc) (instantiate_typing ρ h) hc]
  exact eval_of_normalForm hc hn

/-- …so re-reducing an entry's own value gives back that very entry. -/
theorem reduce_of_reduced (ρ : Env N Tm Ty) (e : EnvEntry N Tm Ty) (hn : NormalForm e.value)
    (h : envCtx ρ ⊢ e.value : e.ty) (hg : Ground e.value) (hτ : Ground e.ty) :
    reduce ρ e.name e.ty h hg hτ = e :=
  EnvEntry.ext rfl rfl (reduce_value_of_reduced ρ e.name e.ty h hg hτ e.typed hn)

/-- A ground declaration's typing, read off the answer of the language's own decision procedure:
on ground input the substitution it answers with changes nothing. -/
theorem typed_of_solution (ρ : Env N Tm Ty) {t : Tm} {τ : Ty} (ht : Ground t) (hτ : Ground τ)
    {σ : Subst Nat Ty}
    (hσ : HasSubst.pSubst (envCtx ρ) σ ⊢ HasSubst.pSubst t σ : HasSubst.pSubst τ σ) :
    envCtx ρ ⊢ t : τ := by
  have h := hasType_of_solution (envCtx_ground ρ) hσ
  rwa [GroundStable.pSubst_ground σ ht, GroundStable.pSubst_ground σ hτ] at h

/-! ## The walk -/

/-- **Reduce one declaration**: check it in the context the environment stands for, inline the
environment into it, and normalize. -/
def evalStep (ρ : Env N Tm Ty) :
    Command N Tm Ty → Except String (Command N Tm Ty × Env N Tm Ty)
  | .decl x τ t =>
      if hg : Ground τ ∧ Ground t then
        match PrincipalElaborate.elaborate (envCtx ρ) t τ with
        | .impossible _ => .error "this declaration does not have its declared type"
        | .mgu _ hσ _ =>
            .ok (.decl x τ (reduce ρ x τ (typed_of_solution ρ hg.2 hg.1 hσ) hg.2 hg.1).value,
              reduce ρ x τ (typed_of_solution ρ hg.2 hg.1 hσ) hg.2 hg.1 :: ρ)
      else .error "this declaration still has metavariables: it is not elaborated"

/-- **The evaluator**: the walk from the empty environment. -/
def evalWalk : Walk (Command N Tm Ty) where
  State := Env N Tm Ty
  init := []
  step := evalStep

/-- What one step produces: the declaration with its body replaced by an entry's value, that entry
pushed on the environment — named and typed as the declaration was, and normal. -/
theorem evalStep_sound {ρ : Env N Tm Ty} {x : N} {τ : Ty} {t : Tm} {d : Command N Tm Ty}
    {ρ' : Env N Tm Ty} (h : evalStep ρ (.decl x τ t) = .ok (d, ρ')) :
    ∃ e : EnvEntry N Tm Ty, e.name = x ∧ e.ty = τ ∧ d = .decl x τ e.value ∧ ρ' = e :: ρ ∧
      NormalForm e.value := by
  simp only [evalStep] at h
  split at h
  · split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, rfl, rfl, rfl, reduce_normal _ _ _ _ _ _⟩
  · cases h

/-- **A reduced declaration steps to itself**, with the same entry. The check succeeds because the
value is closed and typed (`weaken_closed`), and re-reducing it changes nothing
(`reduce_of_reduced`). -/
theorem evalStep_reduced (ρ : Env N Tm Ty) (e : EnvEntry N Tm Ty) (hn : NormalForm e.value) :
    evalStep ρ (.decl e.name e.ty e.value) = .ok (.decl e.name e.ty e.value, e :: ρ) := by
  simp only [evalStep]
  rw [dif_pos ⟨e.tyGround, e.ground⟩]
  split
  · rename_i hno _
    refine absurd ?_ (hno ∅)
    rw [GroundStable.pSubst_ground (∅ : Subst Nat Ty) e.ground,
      GroundStable.pSubst_ground (∅ : Subst Nat Ty) e.tyGround]
    exact LawfulTypeSystem.cong
      (fun y => (Context.pSubst_get?_of_ground (envCtx ρ) ∅ (envCtx_ground ρ) y).symm)
      (HasTermSubst.weaken_closed e.typed)
  · rw [reduce_of_reduced ρ e hn]

/-- **Idempotence, a step at a time.** -/
theorem evalWalk_stepIdempotent : (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).StepIdempotent := by
  intro ρ d d' ρ' h
  obtain ⟨x, τ, t⟩ := d
  obtain ⟨e, rfl, rfl, rfl, rfl, hn⟩ := evalStep_sound h
  exact evalStep_reduced ρ e hn

/-! ## What the walk produces -/

theorem evalRunFrom_sound : ∀ (ρ : Env N Tm Ty) (cs cs' : List (Command N Tm Ty)),
    (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).runFrom ρ cs = .ok cs' →
      HasTypeGround (envCtx ρ) cs'
  | ρ, [], cs', h => by
      simp only [Walk.runFrom, Except.ok.injEq] at h
      subst h
      exact .nil (envCtx_ground ρ)
  | ρ, .decl x τ t :: cs, cs', h => by
      obtain ⟨d, ρ', rest, hs, hr, rfl⟩ := Walk.runFrom_cons_ok _ h
      obtain ⟨e, rfl, rfl, rfl, rfl, _⟩ := evalStep_sound hs
      exact .decl (HasTermSubst.weaken_closed e.typed) e.tyGround e.ground
        (evalRunFrom_sound (e :: ρ) cs rest hr)

/-- **The result is still a well-typed program.** -/
theorem evalWalk_sound {p q : Program N Tm Ty}
    (h : (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).run p = .ok q) : HasType q :=
  evalRunFrom_sound [] _ _ ((Walk.run_eq_ok _).mp h)

/-- Every declaration body is **closed and normal**: no redex left, and no earlier declaration
mentioned.

Closedness is not decoration. Without it idempotence is false — a body could be normal and still
name an earlier declaration, and inlining would change it. -/
def Reduced : List (Command N Tm Ty) → Prop
  | [] => True
  | .decl _ τ t :: cs => NormalForm t ∧ ((Context.empty : Context N Ty) ⊢ t : τ) ∧ Reduced cs

/-- **The result is fully reduced.** -/
theorem evalRunFrom_reduced : ∀ (ρ : Env N Tm Ty) (cs cs' : List (Command N Tm Ty)),
    (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).runFrom ρ cs = .ok cs' → Reduced cs'
  | ρ, [], cs', h => by
      simp only [Walk.runFrom, Except.ok.injEq] at h
      subst h
      trivial
  | ρ, .decl x τ t :: cs, cs', h => by
      obtain ⟨d, ρ', rest, hs, hr, rfl⟩ := Walk.runFrom_cons_ok _ h
      obtain ⟨e, rfl, rfl, rfl, rfl, hn⟩ := evalStep_sound hs
      exact ⟨hn, e.typed, evalRunFrom_reduced (e :: ρ) cs rest hr⟩

/-! ## It never rejects an elaborated program -/

theorem evalRunFrom_ok : ∀ (ρ : Env N Tm Ty) (cs : List (Command N Tm Ty)),
    HasTypeGround (envCtx ρ) cs →
      ∃ out, (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).runFrom ρ cs = .ok out
  | _, [], _ => ⟨[], rfl⟩
  | ρ, .decl x τ t :: cs, h => by
      cases h with
      | decl hty hτ ht hrest =>
          have hstep : (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).step ρ (.decl x τ t)
              = .ok (.decl x τ (reduce ρ x τ hty ht hτ).value, reduce ρ x τ hty ht hτ :: ρ) := by
            show evalStep ρ (.decl x τ t) = _
            simp only [evalStep]
            rw [dif_pos ⟨hτ, ht⟩]
            split
            · rename_i hno _
              refine absurd ?_ (hno ∅)
              rw [GroundStable.pSubst_ground (∅ : Subst Nat Ty) ht,
                GroundStable.pSubst_ground (∅ : Subst Nat Ty) hτ]
              exact LawfulTypeSystem.cong
                (fun y => (Context.pSubst_get?_of_ground (envCtx ρ) ∅ (envCtx_ground ρ) y).symm)
                hty
            · rfl
          obtain ⟨rest, hr⟩ := evalRunFrom_ok (reduce ρ x τ hty ht hτ :: ρ) cs hrest
          exact ⟨_, Walk.runFrom_cons_of _ hstep hr⟩

/-- **Evaluation never rejects a well-typed program** — strong normalization, reached through
`LawfulHasEval`, and the check passing on what elaboration produced. -/
theorem evalWalk_run_ok {p : Program N Tm Ty} (h : HasType p) :
    ∃ q, (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).run p = .ok q := by
  obtain ⟨out, hout⟩ := evalRunFrom_ok [] p.toList h
  have hlen := Walk.runFrom_length _ _ _ _ hout
  match out, hout, hlen with
  | d :: ds, hout, _ => exact ⟨(d, ds), (Walk.run_eq_ok _).mpr hout⟩
  | [], _, hlen => simp [NEList.toList] at hlen

/-! ## After elaboration -/

/-- **The law, as the stage after elaboration**: on programs elaboration leaves unchanged, the
evaluator produces programs elaboration leaves unchanged — they are well-typed — and is idempotent
there, as it is everywhere. -/
theorem evalWalk_lawfulOn [ToString N] :
    (evalWalk (N := N) (Tm := Tm) (Ty := Ty)).LawfulOn
      (fun p => (elabWalk (N := N) (Tm := Tm) (Ty := Ty)).run p = .ok p) where
  preserve _ _ _ h := elabWalk_self (evalWalk_sound h)
  idem p q _ h := Walk.idempotent_of_step _ evalWalk_stepIdempotent p q h

end LambdaLab.TypeSystem.Named.Vernacular
