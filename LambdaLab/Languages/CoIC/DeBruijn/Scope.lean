import LambdaLab.Languages.CoIC.DeBruijn.Inversion

/-!
# CoC — scoping

`t.Scoped n`: every free variable of `t` is below `n`. A well-typed term mentions only variables
its context binds (`HasType.scoped`) — the variable rule finds them there — and in a valid context
so does its type (`HasType.scoped_type`). This is what lets the named calculus read a de Bruijn
term back with names (`Named/Translation.lean`): a scoped term's every variable has a name to read
back to.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

/-- Every free variable is below `n`. -/
def Tm.Scoped : Nat → Tm → Prop
  | n, .var i => i < n
  | _, .sort _ => True
  | n, .pi A B => A.Scoped n ∧ B.Scoped (n + 1)
  | n, .lam A t => A.Scoped n ∧ t.Scoped (n + 1)
  | n, .app t u => t.Scoped n ∧ u.Scoped n

theorem Ctx.lookup_lt : ∀ {Γ : Ctx} {n : Nat} {A : Tm}, Γ.lookup n = some A → n < Γ.length
  | [], _, _, h => by simp [Ctx.lookup] at h
  | _ :: _, 0, _, _ => by simp
  | _ :: Γ, n + 1, _, h => by
      simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at h
      obtain ⟨_, hC, _⟩ := h
      have := Ctx.lookup_lt hC
      simp only [List.length_cons]
      omega

/-- **A well-typed term mentions only its context's variables.** -/
theorem HasType.scoped {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) : t.Scoped Γ.length := by
  induction h with
  | sort => trivial
  | var hn => exact Ctx.lookup_lt hn
  | pi _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | lam _ _ _ ihA iht _ => exact ⟨ihA, iht⟩
  | app _ _ iht ihu => exact ⟨iht, ihu⟩
  | conv _ _ _ iht _ => exact iht

/-- …and so does its type, in a valid context. -/
theorem HasType.scoped_type {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) :
    T.Scoped Γ.length := by
  rcases h.correct hΓ with e | ⟨_, hs⟩
  · subst e; trivial
  · exact hs.scoped

end LambdaLab.Languages.CoIC.DeBruijn
