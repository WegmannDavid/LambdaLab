import LambdaLab.Languages.SystemF.Named.Step
import LambdaLab.Languages.SystemF.DeBruijn.Check

/-!
# System F, named — the typing judgement

`HasType Θ Γ t A`: with the type variables `Θ` in scope and the named term context `Γ` (innermost
first), `t` has type `A`.

    Γ(x) = A                                               ⊢ x : A
    A's type variables in Θ,   Θ; x : A, Γ ⊢ b : B         ⊢ λ x : A . b : A → B
    ⊢ t : A → B,   ⊢ u : A                                 ⊢ t u : B
    β fresh,   β :: Θ; Γ ⊢ b[α := β] : A                   ⊢ Λ α . b : ∀ β . A
    ⊢ t : ∀ α . A,   B's type variables in Θ               ⊢ t [B] : A[α := B]
    ⊢ t : A,   A ≡α A'                                     ⊢ t : A'

Two choices make the judgement independent of the names a term happens to use:

* **a type abstraction is checked at a fresh name.** `β` must be free neither in `Γ` nor in the
  abstraction, so it captures nothing; the body is renamed to it. A term whose binder clashes with a
  variable of the context is therefore still typable, at a renamed binder — no "variable
  convention" is assumed of the input.
* **types are compared up to α** (`conv`): the result of a type abstraction carries whichever
  fresh name was chosen, and `conv` forgets the choice. α-equivalence of types is equality of their
  de Bruijn translations.

## It is de Bruijn typing, read through the translation

`HasType.toDB` and `HasType.ofDB` prove the judgement equivalent to the de Bruijn one on
translations (`hasType_iff_toDB`). Everything proved there arrives here:

* **preservation** (`HasType.preservation`) — exact, not merely up to α, thanks to `conv`;
* **strong normalization** (`HasType.sn`);
* **uniqueness of types up to α** (`HasType.unique`);
* a **decision procedure** (`check`, `check_iff`), the de Bruijn checker on translations.
-/

namespace LambdaLab.Languages.SystemF.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)

variable {N : Type} [Atom N]

/-! ## Contexts -/

/-- A named term context, innermost first. -/
abbrev Ctx (N : Type) := List (N × Ty N)

/-- The type of the innermost binding of `x`. -/
def Ctx.lookup (x : N) : Ctx N → Option (Ty N)
  | [] => none
  | (y, A) :: Γ => if y = x then some A else Ctx.lookup x Γ

def Ctx.names (Γ : Ctx N) : List N := Γ.map Prod.fst

/-- The type variables the context's types mention. -/
def Ctx.ftv (Γ : Ctx N) : List N := Γ.flatMap (fun p => p.2.ftv)

/-- The context's types, translated. -/
def Ctx.toDB (Θ : List N) (Γ : Ctx N) : List DeBruijn.Ty := Γ.map (fun p => p.2.toDB Θ)

theorem Ctx.toDB_getElem? : ∀ (Γ : Ctx N) (Θ : List N) (x : N),
    (Γ.toDB Θ)[lookupVar x Γ.names]? = (Γ.lookup x).map (·.toDB Θ)
  | [], _, _ => by simp [Ctx.toDB, Ctx.names, Ctx.lookup, lookupVar]
  | (y, A) :: Γ, Θ, x => by
      by_cases h : x = y
      · subst h; simp [Ctx.toDB, Ctx.names, Ctx.lookup]
      · have hne : y ≠ x := Ne.symm h
        have := Ctx.toDB_getElem? Γ Θ x
        simp only [Ctx.names, List.map_cons] at this ⊢
        rw [lookupVar_cons_ne _ h]
        simp only [Ctx.toDB, List.map_cons, List.getElem?_cons_succ, Ctx.lookup, hne, if_false]
        exact this

/-- A context does not notice a type binder its types do not mention. -/
theorem Ctx.toDB_insert {Γ : Ctx N} {β : N} (Θ : List N) (h : β ∉ Γ.ftv) :
    Γ.toDB (β :: Θ) = (Γ.toDB Θ).map (DeBruijn.Ty.ren Nat.succ) := by
  simp only [Ctx.toDB, List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp]
  exact Ty.toDB_insert Θ (fun hβ => h (List.mem_flatMap.mpr ⟨p, hp, hβ⟩))

/-! ## Well-formed types -/

/-- **A type is well-formed in `Θ` exactly when its translation is.** -/
theorem Ty.toDB_wf_iff : ∀ (A : Ty N) (Θ : List N),
    (A.toDB Θ).wf Θ.length = true ↔ ∀ α ∈ A.ftv, α ∈ Θ
  | .var α, Θ => by
      simp only [Ty.toDB, DeBruijn.Ty.wf, decide_eq_true_eq, lookupVar_lt_iff, Ty.ftv,
        List.mem_singleton, forall_eq]
  | .arr A B, Θ => by
      simp only [Ty.toDB, DeBruijn.Ty.wf, Bool.and_eq_true, Ty.toDB_wf_iff A Θ, Ty.toDB_wf_iff B Θ,
        Ty.ftv, List.mem_append]
      constructor
      · rintro ⟨h1, h2⟩ α (hα | hα)
        · exact h1 α hα
        · exact h2 α hα
      · intro h
        exact ⟨fun α hα => h α (.inl hα), fun α hα => h α (.inr hα)⟩
  | .all α A, Θ => by
      have := Ty.toDB_wf_iff A (α :: Θ)
      simp only [List.length_cons] at this
      simp only [Ty.toDB, DeBruijn.Ty.wf, this, Ty.ftv, List.mem_filter, List.mem_cons]
      constructor
      · intro h γ ⟨hγ, hne⟩
        rcases h γ hγ with e | h'
        · exact absurd e (by simpa using hne)
        · exact h'
      · intro h γ hγ
        by_cases e : γ = α
        · exact .inl e
        · exact .inr (h γ ⟨hγ, by simpa using e⟩)

/-! ## The judgement -/

/-- **The named typing judgement.** -/
inductive HasType : List N → Ctx N → Tm N → Ty N → Prop
  | var {Θ : List N} {Γ : Ctx N} {x : N} {A : Ty N} :
      Γ.lookup x = some A → HasType Θ Γ (.var x) A
  | lam {Θ : List N} {Γ : Ctx N} {x : N} {A : Ty N} {b : Tm N} {B : Ty N} :
      (∀ α ∈ A.ftv, α ∈ Θ) → HasType Θ ((x, A) :: Γ) b B → HasType Θ Γ (.lam x A b) (.arr A B)
  | app {Θ : List N} {Γ : Ctx N} {t u : Tm N} {A B : Ty N} :
      HasType Θ Γ t (.arr A B) → HasType Θ Γ u A → HasType Θ Γ (.app t u) B
  | tlam {Θ : List N} {Γ : Ctx N} {α : N} {b : Tm N} {β : N} {A : Ty N} :
      β ∉ Γ.ftv → β ∉ (Tm.tlam α b).ftv → HasType (β :: Θ) Γ (b.trename α β) A →
      HasType Θ Γ (.tlam α b) (.all β A)
  | tapp {Θ : List N} {Γ : Ctx N} {t : Tm N} {α : N} {A B : Ty N} :
      HasType Θ Γ t (.all α A) → (∀ γ ∈ B.ftv, γ ∈ Θ) → HasType Θ Γ (.tapp t B) (A.inst α B)
  | conv {Θ : List N} {Γ : Ctx N} {t : Tm N} {A A' : Ty N} :
      HasType Θ Γ t A → A.toDB Θ = A'.toDB Θ → HasType Θ Γ t A'

/-! ## Equivalence with de Bruijn typing -/

/-- **Forward**: a named derivation translates to a de Bruijn one. -/
theorem HasType.toDB {Θ : List N} {Γ : Ctx N} {t : Tm N} {A : Ty N} (h : HasType Θ Γ t A) :
    DeBruijn.HasType Θ.length (Γ.toDB Θ) (t.toDB Θ Γ.names) (A.toDB Θ) := by
  induction h with
  | @var Θ Γ x A hx =>
      refine .var ?_
      rw [Ctx.toDB_getElem?, hx]
      rfl
  | lam hA _ ih => exact .lam ((Ty.toDB_wf_iff _ _).mpr hA) ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | @tlam Θ Γ α b β A hβΓ hβb _ ih =>
      rw [Ctx.toDB_insert Θ hβΓ, Tm.toDB_trename b Θ Γ.names hβb] at ih
      exact .tlam ih
  | @tapp Θ Γ t α A B _ hB ih =>
      rw [Ty.toDB_inst]
      exact .tapp ih ((Ty.toDB_wf_iff _ _).mpr hB)
  | conv _ e ih => rwa [← e]

/-- **Backward**: a de Bruijn derivation for a translation comes from a named one, at a type that
translates to the de Bruijn type. -/
theorem HasType.ofDB : ∀ (t : Tm N) (Θ : List N) (Γ : Ctx N) (T : DeBruijn.Ty),
    DeBruijn.HasType Θ.length (Γ.toDB Θ) (t.toDB Θ Γ.names) T →
      ∃ A : Ty N, A.toDB Θ = T ∧ HasType Θ Γ t A
  | .var x, Θ, Γ, T, h => by
      cases h with
      | var hx =>
          rw [Ctx.toDB_getElem?] at hx
          cases hl : Γ.lookup x with
          | none => rw [hl] at hx; cases hx
          | some A =>
              rw [hl] at hx
              exact ⟨A, Option.some.inj hx, .var hl⟩
  | .lam x A b, Θ, Γ, T, h => by
      cases h with
      | lam hwf hb =>
          obtain ⟨B, hB, hb'⟩ := HasType.ofDB b Θ ((x, A) :: Γ) _ hb
          exact ⟨.arr A B, by simp only [Ty.toDB, hB], .lam ((Ty.toDB_wf_iff _ _).mp hwf) hb'⟩
  | .app t u, Θ, Γ, T, h => by
      cases h with
      | app h₁ h₂ =>
          obtain ⟨At, hAt, ht⟩ := HasType.ofDB t Θ Γ _ h₁
          obtain ⟨Au, hAu, hu⟩ := HasType.ofDB u Θ Γ _ h₂
          cases At with
          | arr A B =>
              simp only [Ty.toDB, DeBruijn.Ty.arr.injEq] at hAt
              exact ⟨B, hAt.2, .app ht (.conv hu (hAu.trans hAt.1.symm))⟩
          | var => simp [Ty.toDB] at hAt
          | all => simp [Ty.toDB] at hAt
  | .tlam α b, Θ, Γ, T, h => by
      cases h with
      | tlam hb =>
          have hβ := freshFor_not_in (Γ.ftv ++ (Tm.tlam α b).ftv)
          generalize freshFor (Γ.ftv ++ (Tm.tlam α b).ftv) = β at hβ
          have hβΓ : β ∉ Γ.ftv := fun e => hβ (List.mem_append_left _ e)
          have hβb : β ∉ (Tm.tlam α b).ftv := fun e => hβ (List.mem_append_right _ e)
          rw [← Ctx.toDB_insert Θ hβΓ, ← Tm.toDB_trename b Θ Γ.names hβb] at hb
          obtain ⟨A, hA, hb'⟩ := HasType.ofDB (b.trename α β) (β :: Θ) Γ _ hb
          exact ⟨.all β A, by simp only [Ty.toDB, hA], .tlam hβΓ hβb hb'⟩
  | .tapp t B, Θ, Γ, T, h => by
      cases h with
      | tapp h₁ hwf =>
          obtain ⟨At, hAt, ht⟩ := HasType.ofDB t Θ Γ _ h₁
          cases At with
          | all α A =>
              simp only [Ty.toDB, DeBruijn.Ty.all.injEq] at hAt
              refine ⟨A.inst α B, ?_, .tapp ht ((Ty.toDB_wf_iff _ _).mp hwf)⟩
              rw [Ty.toDB_inst, hAt]
          | var => simp [Ty.toDB] at hAt
          | arr => simp [Ty.toDB] at hAt
termination_by t => t.size
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Tm.size_trename, Tm.size]; omega)
    | (simp only [Tm.size]; omega)

/-- **The named judgement is de Bruijn typing on translations.** -/
theorem hasType_iff_toDB {Θ : List N} {Γ : Ctx N} {t : Tm N} {A : Ty N} :
    HasType Θ Γ t A ↔ DeBruijn.HasType Θ.length (Γ.toDB Θ) (t.toDB Θ Γ.names) (A.toDB Θ) := by
  constructor
  · exact HasType.toDB
  · intro h
    obtain ⟨A', hA', h'⟩ := HasType.ofDB t Θ Γ _ h
    exact .conv h' hA'

/-! ## What arrives from de Bruijn -/

/-- **Preservation**: a step keeps the type — exactly, the type is not merely α-equivalent. -/
theorem HasType.preservation {Θ : List N} {Γ : Ctx N} {t t' : Tm N} {A : Ty N}
    (h : HasType Θ Γ t A) (hs : Step t t') : HasType Θ Γ t' A :=
  hasType_iff_toDB.mpr (DeBruijn.HasType.preservation (hs.toDB Θ Γ.names) h.toDB)

/-- **Strong normalization**: every well-typed named term is strongly normalizing. -/
theorem HasType.sn {Θ : List N} {Γ : Ctx N} {t : Tm N} {A : Ty N} (h : HasType Θ Γ t A) :
    SN Step t :=
  sn_of_toDB h.toDB.sn

/-- **Types are unique up to α.** -/
theorem HasType.unique {Θ : List N} {Γ : Ctx N} {t : Tm N} {A B : Ty N}
    (hA : HasType Θ Γ t A) (hB : HasType Θ Γ t B) : A.toDB Θ = B.toDB Θ :=
  DeBruijn.HasType.unique hA.toDB hB.toDB

/-- **A decision procedure**: the de Bruijn checker, on translations. -/
def check (Θ : List N) (Γ : Ctx N) (t : Tm N) (A : Ty N) : Bool :=
  DeBruijn.infer Θ.length (Γ.toDB Θ) (t.toDB Θ Γ.names) == some (A.toDB Θ)

theorem check_iff {Θ : List N} {Γ : Ctx N} {t : Tm N} {A : Ty N} :
    check Θ Γ t A = true ↔ HasType Θ Γ t A := by
  rw [hasType_iff_toDB, ← DeBruijn.infer_iff]
  simp [check]

end LambdaLab.Languages.SystemF.Named
