import LambdaLab.Languages.CoIC.DeBruijn.Inversion

/-!
# CoC with inductive types — scoping

`t.Scoped n`: every free variable of `t` is below `n`. A well-typed term mentions only variables
its context binds (`HasType.scoped`) — the variable rule finds them there — and in a valid context
so does its type (`HasType.scoped_type`). This is what lets the named calculus read a de Bruijn
term back with names (`Named/Translation.lean`): a scoped term's every variable has a name to read
back to.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

variable {sg : Sig}

/-- A list whose elements are scoped is scoped. -/
theorem Tm.scoped_of_nth : ∀ {l : Tm} {n : Nat}, l.isList = true →
    (∀ j < l.toList.length, (l.nth j).Scoped n) → l.Scoped n
  | .tnil, _, _, _ => trivial
  | .tcons a l, n, hl, h =>
      ⟨h 0 (by simp [Tm.toList]), Tm.scoped_of_nth hl (fun j hj => h (j + 1)
        (by simp [Tm.toList]; omega))⟩
  | .var _, _, hl, _ => by simp [Tm.isList] at hl
  | .sort _, _, hl, _ => by simp [Tm.isList] at hl
  | .pi _ _, _, hl, _ => by simp [Tm.isList] at hl
  | .lam _ _, _, hl, _ => by simp [Tm.isList] at hl
  | .app _ _, _, hl, _ => by simp [Tm.isList] at hl
  | .ind _, _, hl, _ => by simp [Tm.isList] at hl
  | .ctor _ _ _ _, _, hl, _ => by simp [Tm.isList] at hl
  | .elim _ _ _ _, _, hl, _ => by simp [Tm.isList] at hl

/-- A constructor index below the number of constructors has arguments. -/
theorem Sig.ctorArgs_of_lt {sg : Sig} {i m k : Nat} (hm : sg.numCtors i = some m) (hk : k < m) :
    ∃ c, sg.ctorArgs i k = some c := by
  simp only [Sig.numCtors, Option.map_eq_some_iff] at hm
  obtain ⟨I, hI, rfl⟩ := hm
  exact ⟨I.ctors[k], by simp [Sig.ctorArgs, hI, List.getElem?_eq_getElem hk]⟩

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
theorem HasType.scoped {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) : t.Scoped Γ.length := by
  induction h with
  | sort => trivial
  | var hn => exact Ctx.lookup_lt hn
  | pi _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | lam _ _ _ ihA iht _ => exact ⟨ihA, iht⟩
  | app _ _ iht ihu => exact ⟨iht, ihu⟩
  | conv _ _ _ iht _ => exact iht
  | ind _ => trivial
  | @ctor _ _ _ _ as _ _ _ hl hlen _ iha =>
      exact Tm.scoped_of_nth (l := as) hl (fun j hj => iha j (hlen ▸ hj))
  | @elim _ i m _ bs _ hm _ hl hlen _ _ _ ihC ihb _ iht =>
      refine ⟨ihC, Tm.scoped_of_nth hl (fun k hk => ?_), iht⟩
      obtain ⟨c, hc⟩ := Sig.ctorArgs_of_lt hm (hlen ▸ hk)
      exact ihb k c hc

/-- …and so does its type, in a valid context. -/
theorem HasType.scoped_type {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ) :
    T.Scoped Γ.length := by
  rcases h.correct hΓ with e | ⟨_, hs⟩
  · subst e; trivial
  · exact hs.scoped

end LambdaLab.Languages.CoIC.DeBruijn
