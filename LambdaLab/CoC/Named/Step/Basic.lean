import LambdaLab.CoC.Named.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# Full β-reduction for named CoC

The de Bruijn rules with the capture-avoiding `subst`, and `Conv` as joinability — `refl` and
`symm` now, transitivity deferred to confluence, as on the other side.
-/

namespace LambdaLab.CoC.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

inductive Step : Term N → Term N → Prop where
  | beta  : Step (.app (.lam x A b) a) (b.subst x a)
  | piL   : Step A A' → Step (.pi x A B) (.pi x A' B)
  | piR   : Step B B' → Step (.pi x A B) (.pi x A B')
  | lamTy : Step A A' → Step (.lam x A b) (.lam x A' b)
  | lamB  : Step b b' → Step (.lam x A b) (.lam x A b')
  | appL  : Step f f' → Step (.app f a) (.app f' a)
  | appR  : Step a a' → Step (.app f a) (.app f a')

instance instStep : LambdaLab.TypeSystem.Named.Step (Term N) where
  Step := Step

/-- β-conversion as joinability, exactly as on the de Bruijn side. -/
def Conv (A B : Term N) : Prop :=
  ∃ C : Term N, RTC Step A C ∧ RTC Step B C

theorem Conv.refl (A : Term N) : Conv A A := ⟨A, RTC.refl, RTC.refl⟩

theorem Conv.symm {A B : Term N} (h : Conv A B) : Conv B A :=
  let ⟨C, h₁, h₂⟩ := h
  ⟨C, h₂, h₁⟩

/-- Reduction is conversion — one leg walks, the other stands still. -/
theorem Conv.of_mstep {A B : Term N} (h : RTC Step A B) : Conv A B :=
  ⟨B, h, RTC.refl⟩

end LambdaLab.CoC.Named
