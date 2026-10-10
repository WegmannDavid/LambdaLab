import LambdaLab.Languages.SystemF.DeBruijn.Typing

/-!
# System F — the type checker, sound and complete

`infer Δ Γ t` computes the type of `t`, or fails. Church-style System F carries every annotation it
needs — a `λ` names its argument's type, a type application its argument — so inference is a
structural recursion, and the one comparison it makes (an application's argument against the
function's domain) is syntactic equality of de Bruijn types: there is no α-equivalence to decide.

Both directions are proved against the declarative judgement:

* `infer_sound`: what `infer` returns is a type the term has;
* `infer_complete`: a type the term has is what `infer` returns.

Together, `infer` *decides* the judgement, and types are unique (`HasType.unique`).
-/

namespace LambdaLab.Languages.SystemF.DeBruijn

/-- **Type inference.** -/
def infer (Δ : Nat) (Γ : List Ty) : Tm → Option Ty
  | .var n => Γ[n]?
  | .lam A t =>
      if A.wf Δ then (infer Δ (A :: Γ) t).map (.arr A) else none
  | .app t u =>
      match infer Δ Γ t, infer Δ Γ u with
      | some (.arr A B), some A' => if A = A' then some B else none
      | _, _ => none
  | .tlam t => (infer (Δ + 1) (Γ.map (Ty.ren Nat.succ)) t).map .all
  | .tapp t B =>
      match infer Δ Γ t with
      | some (.all A) => if B.wf Δ then some (A.inst B) else none
      | _ => none

/-- **Soundness**: an inferred type is a type the term has. -/
theorem infer_sound : ∀ {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty},
    infer Δ Γ t = some A → HasType Δ Γ t A
  | _, _, .var _, _, h => .var h
  | Δ, Γ, .lam A₀ t, A, h => by
      simp only [infer] at h
      split at h
      · rename_i hA
        rw [Option.map_eq_some_iff] at h
        obtain ⟨B, hB, rfl⟩ := h
        exact .lam hA (infer_sound hB)
      · cases h
  | Δ, Γ, .app t u, A, h => by
      simp only [infer] at h
      split at h
      · rename_i A₁ B₁ A₂ ht hu
        split at h
        · rename_i heq
          cases h
          subst heq
          exact .app (infer_sound ht) (infer_sound hu)
        · cases h
      · cases h
  | Δ, Γ, .tlam t, A, h => by
      simp only [infer] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨B, hB, rfl⟩ := h
      exact .tlam (infer_sound hB)
  | Δ, Γ, .tapp t B, A, h => by
      simp only [infer] at h
      split at h
      · rename_i A₀ ht
        split at h
        · rename_i hB
          cases h
          exact .tapp (infer_sound ht) hB
        · cases h
      · cases h

/-- **Completeness**: a type the term has is the type `infer` returns. -/
theorem infer_complete {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    infer Δ Γ t = some A := by
  induction h with
  | var hn => exact hn
  | lam hA _ ih => simp only [infer, hA, if_true, ih, Option.map_some]
  | app _ _ ih₁ ih₂ => simp only [infer, ih₁, ih₂, if_true]
  | tlam _ ih => simp only [infer, ih, Option.map_some]
  | tapp _ hB ih => simp only [infer, ih, hB, if_true]

/-- **`infer` decides the judgement.** -/
theorem infer_iff {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} :
    infer Δ Γ t = some A ↔ HasType Δ Γ t A :=
  ⟨infer_sound, infer_complete⟩

/-- **Types are unique.** -/
theorem HasType.unique {Δ : Nat} {Γ : List Ty} {t : Tm} {A B : Ty}
    (hA : HasType Δ Γ t A) (hB : HasType Δ Γ t B) : A = B :=
  Option.some.inj ((infer_complete hA).symm.trans (infer_complete hB))

end LambdaLab.Languages.SystemF.DeBruijn
