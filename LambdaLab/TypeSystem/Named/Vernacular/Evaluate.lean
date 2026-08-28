import LambdaLab.TypeSystem.Named.Vernacular.Typing

/-!
# Running a program

`Elaborate.lean` turns a program into one with no metavariables left; this turns *that* into one
with no work left. Each declaration is reduced in turn, and the result is fully **closed**: the
earlier declarations it mentions have been inlined, and every redex — including the ones inlining
created — is gone.

So this is δ *and* β. The δ half is not decoration: a declared name enters the context as a free
variable, so `λ x . id ( id x )` is already β-normal and β alone would leave almost every program
untouched. Inlining `id` is what turns it into `λ x . x`.

## The fold

Left to right, carrying an environment of the declarations already reduced:

    v₁ = eval t₁
    vᵢ = eval (tᵢ[x₁ := v₁] … [xᵢ₋₁ := vᵢ₋₁])

Substituting the *reduced* values rather than the source bodies is what keeps this linear instead
of exponential in the nesting of definitions, and it is also what makes the result closed at every
step: `t₁` is closed because the first declaration is checked against the empty context, and each
`vᵢ` is closed because everything it could have mentioned has been replaced by something closed.

The environment therefore carries proofs, not just values (`EnvEntry`). They are needed at every
recursive call — `tsubst_typing` wants the value typed, `tsubst_ground` wants it ground — so they
live in the type rather than beside it, where they would have to be threaded as hypotheses through
the definition and all three theorems below.

## Why the derivation is threaded through

`HasEval.eval` takes the typing derivation, because that is where strong normalization comes from.
That does *not* make `evalCommands` a large elimination: it recurses on the command **list**, and
the derivation is passed along as an ordinary argument and taken apart only by the `Prop`-valued
inversion lemmas below. Lean's definitional proof irrelevance then makes the result independent of
*which* derivation was supplied.

## The three facts

Reduction lands in the image and fixes it: the result is well-typed (`evalCommands_hasType`), every
body is reduced (`evalCommands_reduced`), and a program already in that state is left alone
(`evalCommands_of_reduced`). The last is what an `Abstraction` needs for its canonical annotation,
and it is the reason `Reduced` says *closed* and not merely *normal*: on a closed body every
substitution is a no-op by `tsubst_closed`, so the second pass has nothing to do. A body that were
only normal could still mention an earlier name, and inlining it would change the program — the
fixed point would be false.
-/

namespace LambdaLab.TypeSystem.Named.Vernacular

open HasVars (Ground)
open LambdaLab.Nominal (Atom)

/-! Only `[Runnable]`, and no bare `[HasType]`, `[LawfulHasEval]` or `[HasTermSubst]` beside it. A
separate instance variable would be a *second*, unrelated judgement: the derivations the inversion
lemmas produce would not be the ones `eval` and `tsubst` accept, and every application below is a
type error. Same discipline as `Elaborate.lean`, which takes `[PrincipalElaborate]` alone. -/

variable {N Tm Ty : Type} [Atom N] [Runnable N Tm Ty]

/-! ## Inverting the judgement

All `Prop → Prop`, so `cases` on the derivation is allowed; nothing here builds data out of it.
They exist so that `evalCommands` can name the things it needs without repeating the `cases`. -/

/-- The head declaration's body has its declared type. -/
theorem HasTypeGround.head_typed {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) :
    _root_.LambdaLab.TypeSystem.Named.HasType.HasType Γ t τ := by
  cases h with | decl ht _ _ _ => exact ht

/-- The head declaration's body is ground. -/
theorem HasTypeGround.head_ground {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) : Ground t := by
  cases h with | decl _ _ hg _ => exact hg

/-- The head declaration's type is ground. -/
theorem HasTypeGround.head_tyGround {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) : Ground τ := by
  cases h with | decl _ hτ _ _ => exact hτ

/-- The rest of the program types in the extended context. -/
theorem HasTypeGround.tail {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) :
    HasTypeGround (Γ.cons x τ) cs := by
  cases h with | decl _ _ _ hcs => exact hcs

/-! ## The environment -/

/-- A declaration already reduced: its value, with the two facts every later declaration needs of
it. `typed` in the **empty** context is the closedness that makes inlining idempotent. -/
structure EnvEntry (N Tm Ty : Type) [Atom N] [Runnable N Tm Ty] where
  /-- The name it was declared under. -/
  name : N
  /-- Its declared type. -/
  ty : Ty
  /-- Its reduced body. -/
  value : Tm
  /-- Closed at its declared type. -/
  typed : (Context.empty : Context N Ty) ⊢ value : ty
  /-- And holding no metavariable, which `HasTypeGround` demands of every body. -/
  ground : Ground value

/-- The declarations reduced so far, **most recent first** — so the head is the outermost `cons` of
the context they stand for, which is the end `tsubst_typing` peels. -/
abbrev Env (N Tm Ty : Type) [Atom N] [Runnable N Tm Ty] := List (EnvEntry N Tm Ty)

/-- The context an environment stands for. -/
def envCtx : Env N Tm Ty → Context N Ty
  | [] => Context.empty
  | e :: ρ => (envCtx ρ).cons e.name e.ty

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

/-! ## The reducer -/

/-- One declaration reduced, packaged as the environment entry the next one will use. Split out of
`evalCommands` so that the value and its two proofs are named once rather than three times. -/
def reduce (ρ : Env N Tm Ty) (x : N) (τ : Ty) {t : Tm} (h : envCtx ρ ⊢ t : τ) (hg : Ground t) :
    EnvEntry N Tm Ty :=
  { name := x, ty := τ
    value := HasEval.eval Context.empty (instantiate ρ t) τ (instantiate_typing ρ h)
    typed := preservation_mstep (instantiate_typing ρ h)
      (LawfulHasEval.evalReachable (instantiate_typing ρ h))
    ground := LawfulHasEval.evalGround (instantiate_typing ρ h) (instantiate_ground ρ hg) }

/-- The reduced value admits no further reduction. -/
theorem reduce_normal (ρ : Env N Tm Ty) (x : N) (τ : Ty) {t : Tm} (h : envCtx ρ ⊢ t : τ)
    (hg : Ground t) : NormalForm (reduce ρ x τ h hg).value :=
  LawfulHasEval.evalNormal (instantiate_typing ρ h)

/-- **Reducing a body that is already closed and normal returns it.** Inlining is a no-op on it
(`instantiate_closed`) and so is evaluation (`eval_of_normalForm`). -/
theorem reduce_value_of_reduced (ρ : Env N Tm Ty) (x : N) (τ : Ty) {t : Tm}
    (h : envCtx ρ ⊢ t : τ) (hg : Ground t) (hc : (Context.empty : Context N Ty) ⊢ t : τ)
    (hn : NormalForm t) : (reduce ρ x τ h hg).value = t := by
  show HasEval.eval Context.empty (instantiate ρ t) τ (instantiate_typing ρ h) = t
  -- The derivation mentions `instantiate ρ t` too, so `rw` cannot move the term alone;
  -- `eval_congr` moves both at once.
  rw [eval_congr (instantiate_closed ρ hc) (instantiate_typing ρ h) hc]
  exact eval_of_normalForm hc hn

/-- **Reduce every declaration**, each in the environment its predecessors built. -/
def evalCommands : (ρ : Env N Tm Ty) → (cs : List (Command N Tm Ty)) →
    HasTypeGround (envCtx ρ) cs → List (Command N Tm Ty)
  | _, [], _ => []
  | ρ, Command.decl x τ _ :: cs, h =>
      Command.decl x τ (reduce ρ x τ h.head_typed h.head_ground).value
        :: evalCommands (reduce ρ x τ h.head_typed h.head_ground :: ρ) cs h.tail

/-! ## Fully reduced -/

/-- Every declaration body is **closed and normal**: no redex left, and no earlier declaration
mentioned. The image of `evalCommands`.

Closedness is not decoration. Without it the fixed point below is false — a body could be normal
and still name an earlier declaration, and inlining would change it. -/
def Reduced : List (Command N Tm Ty) → Prop
  | [] => True
  | Command.decl _ τ t :: cs =>
      NormalForm t ∧ ((Context.empty : Context N Ty) ⊢ t : τ) ∧ Reduced cs

/-- A whole program is reduced when its command list is. -/
abbrev AllReduced (p : Program N Tm Ty) : Prop := Reduced p.toList

/-- **The result is still a well-typed program.** Each body is now closed, and `weaken_closed`
puts it back under the context `HasTypeGround` checks it against. -/
theorem evalCommands_hasType : ∀ (ρ : Env N Tm Ty) (cs : List (Command N Tm Ty))
    (h : HasTypeGround (envCtx ρ) cs), HasTypeGround (envCtx ρ) (evalCommands ρ cs h)
  | _, [], h => h
  | ρ, Command.decl x τ _ :: cs, h =>
      HasTypeGround.decl
        (HasTermSubst.weaken_closed (reduce ρ x τ h.head_typed h.head_ground).typed)
        h.head_tyGround
        (reduce ρ x τ h.head_typed h.head_ground).ground
        (evalCommands_hasType (reduce ρ x τ h.head_typed h.head_ground :: ρ) cs h.tail)

/-- **The result is fully reduced** — normal by `evalNormal`, closed by construction. -/
theorem evalCommands_reduced : ∀ (ρ : Env N Tm Ty) (cs : List (Command N Tm Ty))
    (h : HasTypeGround (envCtx ρ) cs), Reduced (evalCommands ρ cs h)
  | _, [], _ => trivial
  | ρ, Command.decl x τ _ :: cs, h =>
      ⟨reduce_normal ρ x τ h.head_typed h.head_ground,
        (reduce ρ x τ h.head_typed h.head_ground).typed,
        evalCommands_reduced (reduce ρ x τ h.head_typed h.head_ground :: ρ) cs h.tail⟩

/-- **The fixed point.** A program whose bodies are already closed and normal is returned
unchanged — which is what lets an `Abstraction` onto the reduced programs take each value as its
own canonical re-presentation. -/
theorem evalCommands_of_reduced : ∀ (ρ : Env N Tm Ty) (cs : List (Command N Tm Ty))
    (h : HasTypeGround (envCtx ρ) cs), Reduced cs → evalCommands ρ cs h = cs
  | _, [], _, _ => rfl
  | ρ, Command.decl x τ t :: cs, h, hr => by
      show Command.decl x τ (reduce ρ x τ h.head_typed h.head_ground).value
          :: evalCommands (reduce ρ x τ h.head_typed h.head_ground :: ρ) cs h.tail
        = Command.decl x τ t :: cs
      rw [reduce_value_of_reduced ρ x τ h.head_typed h.head_ground hr.2.1 hr.1,
        evalCommands_of_reduced (reduce ρ x τ h.head_typed h.head_ground :: ρ) cs h.tail hr.2.2]

/-! ## At the level of programs

`Program` is a `NEList`, i.e. a head and a tail, and `evalCommands` never shortens a list — so the
reduced program is non-empty for the same reason the input was, and the head/tail split survives
without a separate argument. `envCtx []` is `Context.empty`, which is where `HasType` starts. -/

/-- **Reduce a program.** -/
def evalProgram : (p : Program N Tm Ty) → HasType p → Program N Tm Ty
  | (Command.decl x τ _, cs), h =>
      (Command.decl x τ (reduce [] x τ h.head_typed h.head_ground).value,
        evalCommands [reduce [] x τ h.head_typed h.head_ground] cs h.tail)

/-- The reduced program is still well-typed. -/
theorem evalProgram_hasType : ∀ (p : Program N Tm Ty) (h : HasType p),
    HasType (evalProgram p h)
  | (Command.decl x τ _, cs), h =>
      HasTypeGround.decl
        (HasTermSubst.weaken_closed (reduce [] x τ h.head_typed h.head_ground).typed)
        h.head_tyGround
        (reduce [] x τ h.head_typed h.head_ground).ground
        (evalCommands_hasType [reduce [] x τ h.head_typed h.head_ground] cs h.tail)

/-- Every body of the reduced program is closed and normal. -/
theorem evalProgram_allReduced : ∀ (p : Program N Tm Ty) (h : HasType p),
    AllReduced (evalProgram p h)
  | (Command.decl x τ _, cs), h =>
      ⟨reduce_normal [] x τ h.head_typed h.head_ground,
        (reduce [] x τ h.head_typed h.head_ground).typed,
        evalCommands_reduced [reduce [] x τ h.head_typed h.head_ground] cs h.tail⟩

/-- **The fixed point, at the level of programs.** -/
theorem evalProgram_of_allReduced : ∀ (p : Program N Tm Ty) (h : HasType p),
    AllReduced p → evalProgram p h = p
  | (Command.decl x τ t, cs), h, hr => by
      show ((Command.decl x τ (reduce [] x τ h.head_typed h.head_ground).value :
              Command N Tm Ty),
            evalCommands [reduce [] x τ h.head_typed h.head_ground] cs h.tail)
        = (Command.decl x τ t, cs)
      rw [reduce_value_of_reduced [] x τ h.head_typed h.head_ground hr.2.1 hr.1,
        evalCommands_of_reduced [reduce [] x τ h.head_typed h.head_ground] cs h.tail hr.2.2]

end LambdaLab.TypeSystem.Named.Vernacular
