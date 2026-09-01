import LambdaLab.CoC.DeBruijn.Basic
import LambdaLab.TypeSystem.Named.Basic

/-!
# Full β-reduction for CoC

One β and congruence everywhere — under `λ`, under `Π` (types reduce too: the conversion rule
needs it), on both sides of an application, and in annotations. One rule set for the one
syntactic category, where System F needed two β's.
-/

namespace LambdaLab.CoC.DeBruijn

inductive Step : Term → Term → Prop where
  | beta  : Step (.app (.lam A b) a) (b.subst 0 a)
  | piL   : Step A A' → Step (.pi A B) (.pi A' B)
  | piR   : Step B B' → Step (.pi A B) (.pi A B')
  | lamTy : Step A A' → Step (.lam A b) (.lam A' b)
  | lamB  : Step b b' → Step (.lam A b) (.lam A b')
  | appL  : Step f f' → Step (.app f a) (.app f' a)
  | appR  : Step a a' → Step (.app f a) (.app f a')

instance instStep : LambdaLab.TypeSystem.Named.Step Term where
  Step := Step

/-- **β-conversion, as joinability**: two terms convert when they reach a common reduct. This is
the form confluence makes equivalent to full symmetric-transitive conversion, and it is the
cleaner one to state and to invert; the equivalence becomes a theorem when confluence lands. -/
def Conv (A B : Term) : Prop :=
  ∃ C : Term, RTC Step A C ∧ RTC Step B C

theorem Conv.refl (A : Term) : Conv A A := ⟨A, RTC.refl, RTC.refl⟩

theorem Conv.symm {A B : Term} (h : Conv A B) : Conv B A :=
  let ⟨C, h₁, h₂⟩ := h
  ⟨C, h₂, h₁⟩

/-- Reduction is conversion — one leg walks, the other stands still. -/
theorem Conv.of_mstep {A B : Term} (h : RTC Step A B) : Conv A B :=
  ⟨B, h, RTC.refl⟩

end LambdaLab.CoC.DeBruijn
