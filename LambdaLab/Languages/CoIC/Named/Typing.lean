import LambdaLab.Languages.CoIC.Named.Step
import LambdaLab.Languages.CoIC.DeBruijn.Check

/-!
# CoIC, named — the typing judgement

`HasType sg Γ t A`: over the signature `sg`, in the named context `Γ` (innermost first), `t` has type `A`.

    ───────────────          Γ(x) = A
     Γ ⊢ * : □               ─────────
                              Γ ⊢ x : A

     Γ ⊢ A : s₁    z fresh    z : A, Γ ⊢ B[x := z] : s₂
    ─────────────────────────────────────────────────────
                    Γ ⊢ Π x : A . B : s₂

     Γ ⊢ A : s₁    z fresh    z : A, Γ ⊢ b[x := z] : B    z : A, Γ ⊢ B : s₂
    ─────────────────────────────────────────────────────────────────────────
                         Γ ⊢ λ x : A . b : Π z : A . B

     Γ ⊢ t : Π x : A . B    Γ ⊢ u : A        Γ ⊢ t : A    Γ ⊢ B : s    A ≡ B
    ───────────────────────────────────      ──────────────────────────────────
           Γ ⊢ t u : B[x := u]                         Γ ⊢ t : B

     Γ ⊢ t : A    A =α B
    ────────────────────
         Γ ⊢ t : B

## Inductive types

`ind`, `ctor` and `elim` are the de Bruijn rules (`DeBruijn/Typing.lean`) over the same signature.
Where those name a type built from the signature — a constructor's argument type, a branch type —
the named rule takes every named type that translates to it, so no named version of the
signature's types needs to be built.

## Binders are checked at a fresh name

Every binder may occur in types, so a body is checked under its binder renamed to a name
`z` free neither in the context nor in the term. A term whose binder clashes with a context
variable is therefore still typable — at a renamed binder — and no "variable convention" is
assumed of the input. A context built this way has no repeated names, and each entry's type
mentions only names further out; `Ctx.Wf` records exactly that, with the entry typed.

## Conversion is through the translation

`Conv Γ A B` is convertibility of the translations — β-conversion up to α, which is what named
reduction (`Step.lean`) is, read through the translation. The `alpha` rule compares types up to
bound names alone, needing no sort for the target.

## It is de Bruijn typing, read through the translation

`HasType.toDB` and `HasType.ofDB` prove the judgement equivalent to the de Bruijn one on
translations, in a valid context (`hasType_iff_toDB`). The backward direction reads intermediate
de Bruijn types back with names (`fromDB`). Everything proved there arrives here:

* **subject reduction** (`HasType.preservation`);
* **strong normalization** (`HasType.sn`);
* **uniqueness of types up to conversion** (`HasType.unique`);
* a **decision procedure** (`decHasType`) — the de Bruijn checker, on translations.
-/

namespace LambdaLab.Languages.CoIC.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)
open LambdaLab (SN)
open LambdaLab.Languages.CoIC.DeBruijn (Srt argTy branchTy)

variable {N : Type} [Atom N] {sg : DeBruijn.Sig}

/-! ## Contexts -/

/-- A named context, innermost first. -/
abbrev Ctx (N : Type) := List (N × Tm N)

/-- The type of the innermost binding of `x`. -/
def Ctx.lookup : Ctx N → N → Option (Tm N)
  | [], _ => none
  | (y, A) :: Γ, x => if y = x then some A else Ctx.lookup Γ x

def Ctx.names (Γ : Ctx N) : List N := Γ.map Prod.fst

omit [Atom N] in
@[simp] theorem Ctx.names_cons (x : N) (A : Tm N) (Γ : Ctx N) :
    Ctx.names ((x, A) :: Γ) = x :: Ctx.names Γ := rfl

/-- The context, translated: each entry against the names further out. -/
def Ctx.toDB : Ctx N → DeBruijn.Ctx
  | [] => []
  | (_, A) :: Γ => A.toDB (Ctx.names Γ) :: Ctx.toDB Γ

theorem Ctx.length_toDB : ∀ Γ : Ctx N, (Ctx.toDB Γ).length = (Ctx.names Γ).length
  | [] => rfl
  | (_, _) :: Γ => by simp [Ctx.toDB, Ctx.length_toDB Γ]

theorem Ctx.lookup_of_mem : ∀ {Γ : Ctx N} {x : N}, x ∈ Ctx.names Γ → ∃ A, Γ.lookup x = some A
  | [], _, h => by simp [Ctx.names] at h
  | (y, A) :: Γ, x, h => by
      by_cases e : y = x
      · exact ⟨A, by simp [Ctx.lookup, e]⟩
      · simp only [Ctx.names_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm e
        · obtain ⟨B, hB⟩ := Ctx.lookup_of_mem h
          exact ⟨B, by simp [Ctx.lookup, e, hB]⟩

/-- **Conversion**, of the translations. -/
def Conv (Γ : Ctx N) (A B : Tm N) : Prop := DeBruijn.Conv (A.toDB Γ.names) (B.toDB Γ.names)

/-! ## The judgement -/

/-- **The named typing judgement.** -/
inductive HasType (sg : DeBruijn.Sig) : Ctx N → Tm N → Tm N → Prop
  | sort {Γ : Ctx N} : HasType sg Γ (.sort .star) (.sort .box)
  | var {Γ : Ctx N} {x : N} {A : Tm N} : Γ.lookup x = some A → HasType sg Γ (.var x) A
  | pi {Γ : Ctx N} {x z : N} {A B : Tm N} {s₁ s₂ : Srt} :
      HasType sg Γ A (.sort s₁) → z ∉ Γ.names → z ∉ (Tm.pi x A B).fv →
      HasType sg ((z, A) :: Γ) (B.rename x z) (.sort s₂) → HasType sg Γ (.pi x A B) (.sort s₂)
  | lam {Γ : Ctx N} {x z : N} {A b B : Tm N} {s₁ s₂ : Srt} :
      HasType sg Γ A (.sort s₁) → z ∉ Γ.names → z ∉ (Tm.lam x A b).fv →
      HasType sg ((z, A) :: Γ) (b.rename x z) B → HasType sg ((z, A) :: Γ) B (.sort s₂) →
      HasType sg Γ (.lam x A b) (.pi z A B)
  | app {Γ : Ctx N} {t u : Tm N} {x : N} {A B : Tm N} :
      HasType sg Γ t (.pi x A B) → HasType sg Γ u A → HasType sg Γ (.app t u) (B.inst x u)
  | conv {Γ : Ctx N} {t A B : Tm N} {s : Srt} :
      HasType sg Γ t A → HasType sg Γ B (.sort s) → Conv Γ A B → HasType sg Γ t B
  | alpha {Γ : Ctx N} {t A B : Tm N} :
      HasType sg Γ t A → A.toDB Γ.names = B.toDB Γ.names → HasType sg Γ t B
  | ind {Γ : Ctx N} {i : Nat} : i < sg.length → HasType sg Γ (.ind i) (.sort .star)
  | ctor {Γ : Ctx N} {i k : Nat} {mask : List Bool} {as : Tm N} {c : DeBruijn.CtorSpec} :
      sg.ctorArgs i k = some c → mask = c.mask → as.isList = true → as.toList.length = c.length →
      (∀ j < c.length, ∀ A : Tm N, A.toDB Γ.names = argTy i (c.getD j none) →
        HasType sg Γ (as.nth j) A) →
      HasType sg Γ (.ctor i k mask as) (.ind i)
  | elim {Γ : Ctx N} {i m : Nat} {C bs t : Tm N} :
      sg.numCtors i = some m → HasType sg Γ C (.sort .star) → bs.isList = true →
      bs.toList.length = m →
      (∀ k c, sg.ctorArgs i k = some c → ∀ B : Tm N,
        B.toDB Γ.names = branchTy i c (C.toDB Γ.names) → HasType sg Γ (bs.nth k) B) →
      (∀ k c, sg.ctorArgs i k = some c → ∀ o ∈ c, ∀ A : Tm N, A.toDB Γ.names = argTy i o →
        HasType sg Γ A (.sort .star)) →
      HasType sg Γ t (.ind i) → HasType sg Γ (.elim i C bs t) C

/-- **A valid context**: no repeated names, each entry's type mentions only names further out and
is typed there. -/
def Ctx.Wf (sg : DeBruijn.Sig) : Ctx N → Prop
  | [] => True
  | (x, A) :: Γ => Ctx.Wf sg Γ ∧ x ∉ Ctx.names Γ ∧ (∀ y ∈ A.fv, y ∈ Ctx.names Γ) ∧
      ∃ s, HasType sg Γ A (.sort s)

theorem Ctx.Wf.nodup : ∀ {Γ : Ctx N}, Ctx.Wf sg Γ → (Ctx.names Γ).Nodup
  | [], _ => List.nodup_nil
  | (_, _) :: _, ⟨hΓ, hx, _, _⟩ => List.nodup_cons.mpr ⟨hx, Ctx.Wf.nodup hΓ⟩

/-- A looked-up type mentions only the context's names. -/
theorem Ctx.Wf.lookup_fv : ∀ {Γ : Ctx N}, Ctx.Wf sg Γ → ∀ {x : N} {A : Tm N}, Γ.lookup x = some A →
    ∀ y ∈ A.fv, y ∈ Ctx.names Γ
  | [], _, _, _, h => by simp [Ctx.lookup] at h
  | (z, B) :: Γ, ⟨hΓ, _, hB, _⟩, x, A, h => by
      simp only [Ctx.lookup] at h
      intro y hy
      split at h
      · cases h; exact List.mem_cons_of_mem _ (hB y hy)
      · exact List.mem_cons_of_mem _ (Ctx.Wf.lookup_fv hΓ h y hy)

/-- **Lookup commutes with the translation**, in a valid context. -/
theorem Ctx.Wf.lookup_toDB : ∀ {Γ : Ctx N}, Ctx.Wf sg Γ → ∀ {x : N} {A : Tm N},
    Γ.lookup x = some A → (Ctx.toDB Γ).lookup (lookupVar x Γ.names) = some (A.toDB Γ.names)
  | [], _, _, _, h => by simp [Ctx.lookup] at h
  | (y, B) :: Γ, ⟨hΓ, hy, hB, _⟩, x, A, h => by
      simp only [Ctx.lookup] at h
      split at h
      · rename_i e
        cases h
        subst e
        simp only [Ctx.names_cons, lookupVar_cons_self, Ctx.toDB, DeBruijn.Ctx.lookup_zero]
        rw [Tm.toDB_insert _ (fun h' => hy (hB y h'))]
      · rename_i e
        have hne : x ≠ y := fun e' => e e'.symm
        simp only [Ctx.names_cons, lookupVar_cons_ne _ hne, Ctx.toDB,
          DeBruijn.Ctx.lookup_succ, Ctx.Wf.lookup_toDB hΓ h, Option.map_some]
        rw [Tm.toDB_insert _ (fun h' => hy (Ctx.Wf.lookup_fv hΓ h y h'))]

/-! ## Forward: named derivations translate -/

/-- A constructor's argument types are closed. -/
theorem argTy_getD_closed {i k : Nat} {c : DeBruijn.CtorSpec} (hc : sg.ctorArgs i k = some c)
    (j : Nat) : (argTy i (c.getD j none)).Scoped 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : c[j]? with
  | none => trivial
  | some o => exact DeBruijn.Sig.ctorArgs_closed hc o (List.mem_of_getElem? h)

/-- **Forward**: in a valid context, a named derivation translates to a de Bruijn one. -/
theorem HasType.toDB {Γ : Ctx N} {t T : Tm N} (h : HasType sg Γ t T) :
    Ctx.Wf sg Γ → DeBruijn.HasType sg (Ctx.toDB Γ) (t.toDB Γ.names) (T.toDB Γ.names) := by
  induction h with
  | sort => intro _; exact .sort
  | var hx => intro hΓ; exact .var (hΓ.lookup_toDB hx)
  | @pi Γ x z A B s₁ s₂ hA hz hzf _ ihA ihB =>
      intro hΓ
      have dA := ihA hΓ
      have hsc : ∀ y ∈ A.fv, y ∈ Γ.names :=
        Tm.fv_of_scoped A _ (by have := dA.scoped; rwa [Ctx.length_toDB] at this)
      have dB := ihB ⟨hΓ, hz, hsc, s₁, hA⟩
      simp only [Ctx.names_cons, Ctx.toDB] at dB
      rw [Tm.toDB_rename B _ (fun e => hzf (by simp only [Tm.fv]; exact List.mem_append_right _ e))]
        at dB
      exact .pi dA dB
  | @lam Γ x z A b B s₁ s₂ hA hz hzf _ _ ihA ihb ihB =>
      intro hΓ
      have dA := ihA hΓ
      have hsc : ∀ y ∈ A.fv, y ∈ Γ.names :=
        Tm.fv_of_scoped A _ (by have := dA.scoped; rwa [Ctx.length_toDB] at this)
      have hΓ' : Ctx.Wf sg ((z, A) :: Γ) := ⟨hΓ, hz, hsc, s₁, hA⟩
      have db := ihb hΓ'
      have dB := ihB hΓ'
      simp only [Ctx.names_cons, Ctx.toDB] at db dB
      rw [Tm.toDB_rename b _ (fun e => hzf (by simp only [Tm.fv]; exact List.mem_append_right _ e))]
        at db
      exact .lam dA db dB
  | app _ _ iht ihu =>
      intro hΓ
      rw [Tm.toDB_inst]
      exact .app (iht hΓ) (ihu hΓ)
  | conv _ _ hc iht ihB => intro hΓ; exact .conv (iht hΓ) (ihB hΓ) hc
  | alpha _ e iht => intro hΓ; rw [← e]; exact iht hΓ
  | ind hi => intro _; exact .ind hi
  | @ctor Γ i k mask as c hc hm hl hlen _ ih =>
      intro hΓ
      refine .ctor hc hm (by rw [Tm.isList_toDB]; exact hl)
        (by rw [Tm.toList_toDB, List.length_map]; exact hlen) (fun j hj => ?_)
      obtain ⟨A, hA⟩ := exists_closed (N := N) (argTy_getD_closed hc j)
      have := ih j hj A (hA _) hΓ
      rwa [hA, ← Tm.nth_toDB] at this
  | @elim Γ i m C bs t hm _ hl hlen _ _ _ ihC ihb iha iht =>
      intro hΓ
      have dC := ihC hΓ
      have hargs : ∀ k c, sg.ctorArgs i k = some c → ∀ o ∈ c,
          DeBruijn.HasType sg (Ctx.toDB Γ) (argTy i o) (.sort .star) := fun k c hc o ho => by
        obtain ⟨A, hA⟩ := exists_closed (N := N) (DeBruijn.Sig.ctorArgs_closed hc o ho)
        have := iha k c hc o ho A (hA _) hΓ
        rwa [hA] at this
      refine .elim hm dC (by rw [Tm.isList_toDB]; exact hl)
        (by rw [Tm.toList_toDB, List.length_map]; exact hlen) (fun k c hc => ?_) hargs (iht hΓ)
      have hsc := (DeBruijn.HasType.branchTy_sort (hargs k c hc) dC).scoped
      rw [Ctx.length_toDB] at hsc
      obtain ⟨B, hB⟩ := exists_toDB (N := N) hΓ.nodup hsc
      have := ihb k c hc B hB hΓ
      rwa [hB, ← Tm.nth_toDB] at this

/-- A valid named context translates to a valid de Bruijn one. -/
theorem Ctx.Wf.toDB : ∀ {Γ : Ctx N}, Ctx.Wf sg Γ → DeBruijn.Wf sg (Ctx.toDB Γ)
  | [], _ => trivial
  | (_, _) :: _, ⟨hΓ, _, _, s, hA⟩ => ⟨Ctx.Wf.toDB hΓ, s, hA.toDB hΓ⟩

/-! ## Backward: de Bruijn derivations of translations come from named ones -/

theorem Tm.toDB_eq_sort {t : Tm N} {ns : List N} {s : Srt} (h : t.toDB ns = .sort s) :
    t = .sort s := by
  cases t <;> simp_all [Tm.toDB]

theorem Tm.toDB_eq_var {t : Tm N} {ns : List N} {n : Nat} (h : t.toDB ns = .var n) :
    ∃ x, t = .var x ∧ lookupVar x ns = n := by
  cases t <;> simp_all [Tm.toDB]

theorem Tm.toDB_eq_pi {t : Tm N} {ns : List N} {A' B' : DeBruijn.Tm} (h : t.toDB ns = .pi A' B') :
    ∃ x A B, t = .pi x A B ∧ A.toDB ns = A' ∧ B.toDB (x :: ns) = B' := by
  cases t with
  | pi x A B =>
      simp only [Tm.toDB, DeBruijn.Tm.pi.injEq] at h
      exact ⟨x, A, B, rfl, h.1, h.2⟩
  | _ => simp [Tm.toDB] at h

theorem Tm.toDB_eq_lam {t : Tm N} {ns : List N} {A' b' : DeBruijn.Tm}
    (h : t.toDB ns = .lam A' b') :
    ∃ x A b, t = .lam x A b ∧ A.toDB ns = A' ∧ b.toDB (x :: ns) = b' := by
  cases t with
  | lam x A b =>
      simp only [Tm.toDB, DeBruijn.Tm.lam.injEq] at h
      exact ⟨x, A, b, rfl, h.1, h.2⟩
  | _ => simp [Tm.toDB] at h

theorem Tm.toDB_eq_app {t : Tm N} {ns : List N} {f' u' : DeBruijn.Tm}
    (h : t.toDB ns = .app f' u') : ∃ f u, t = .app f u ∧ f.toDB ns = f' ∧ u.toDB ns = u' := by
  cases t with
  | app f u =>
      simp only [Tm.toDB, DeBruijn.Tm.app.injEq] at h
      exact ⟨f, u, rfl, h.1, h.2⟩
  | _ => simp [Tm.toDB] at h

theorem Tm.toDB_eq_ind {t : Tm N} {ns : List N} {i : Nat} (h : t.toDB ns = .ind i) :
    t = .ind i := by
  cases t <;> simp_all [Tm.toDB]

theorem Tm.toDB_eq_ctor {t : Tm N} {ns : List N} {i k : Nat} {m : List Bool} {as' : DeBruijn.Tm}
    (h : t.toDB ns = .ctor i k m as') : ∃ as, t = .ctor i k m as ∧ as.toDB ns = as' := by
  cases t with
  | ctor i' k' m' as =>
      simp only [Tm.toDB, DeBruijn.Tm.ctor.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨as, rfl, rfl⟩
  | _ => simp [Tm.toDB] at h

theorem Tm.toDB_eq_elim {t : Tm N} {ns : List N} {i : Nat} {C' bs' t' : DeBruijn.Tm}
    (h : t.toDB ns = .elim i C' bs' t') :
    ∃ C bs t₀, t = .elim i C bs t₀ ∧ C.toDB ns = C' ∧ bs.toDB ns = bs' ∧ t₀.toDB ns = t' := by
  cases t with
  | elim i' C bs t₀ =>
      simp only [Tm.toDB, DeBruijn.Tm.elim.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨C, bs, t₀, rfl, rfl, rfl, rfl⟩
  | _ => simp [Tm.toDB] at h

/-- **Backward**: a de Bruijn derivation for translations, in a valid context, comes from a named
one — at the very types it names. -/
theorem HasType.ofDB {Δ : DeBruijn.Ctx} {t' T' : DeBruijn.Tm} (h : DeBruijn.HasType sg Δ t' T') :
    ∀ (Γ : Ctx N), Ctx.toDB Γ = Δ → Ctx.Wf sg Γ → ∀ (t T : Tm N), t.toDB Γ.names = t' →
      T.toDB Γ.names = T' → HasType sg Γ t T := by
  induction h with
  | sort =>
      intro Γ _ _ t T ht hT
      rw [Tm.toDB_eq_sort ht, Tm.toDB_eq_sort hT]
      exact .sort
  | @var Δ n A' hn =>
      intro Γ hΔ hΓ t T ht hT
      obtain ⟨x, rfl, hx⟩ := Tm.toDB_eq_var ht
      subst hΔ
      have hlt : lookupVar x Γ.names < Γ.names.length := by
        rw [hx, ← Ctx.length_toDB]; exact DeBruijn.Ctx.lookup_lt hn
      obtain ⟨A, hA⟩ := Ctx.lookup_of_mem (lookupVar_lt_iff.mp hlt)
      have e := hΓ.lookup_toDB hA
      rw [hx, hn] at e
      exact .alpha (.var hA) ((Option.some.inj e).symm.trans hT.symm)
  | @pi Δ A' B' s₁ s₂ hA' _ ihA ihB =>
      intro Γ hΔ hΓ t T ht hT
      obtain ⟨x, A, B, rfl, hA, hB⟩ := Tm.toDB_eq_pi ht
      rw [Tm.toDB_eq_sort hT]
      have dA := ihA Γ hΔ hΓ A (.sort s₁) hA rfl
      have hsc : ∀ y ∈ A.fv, y ∈ Γ.names := Tm.fv_of_scoped A _ (by
        rw [hA, ← Ctx.length_toDB, hΔ]; exact hA'.scoped)
      have hz := freshFor_not_in (Γ.names ++ (Tm.pi x A B).fv)
      generalize freshFor (Γ.names ++ (Tm.pi x A B).fv) = z at hz
      have hzn : z ∉ Γ.names := fun e => hz (List.mem_append_left _ e)
      have hzf : z ∉ (Tm.pi x A B).fv := fun e => hz (List.mem_append_right _ e)
      refine .pi dA hzn hzf (ihB ((z, A) :: Γ) (by simp [Ctx.toDB, hA, hΔ]) ⟨hΓ, hzn, hsc, s₁, dA⟩
        _ _ ?_ rfl)
      simp only [Ctx.names_cons]
      rw [Tm.toDB_rename B _ (fun e => hzf (by simp only [Tm.fv]; exact List.mem_append_right _ e)),
        hB]
  | @lam Δ A' b' B' s₁ s₂ hA' _ _ ihA ihb ihB =>
      intro Γ hΔ hΓ t T ht hT
      obtain ⟨x, A, b, rfl, hA, hb⟩ := Tm.toDB_eq_lam ht
      obtain ⟨y, A₁, B₁, rfl, hA₁, hB₁⟩ := Tm.toDB_eq_pi hT
      have dA := ihA Γ hΔ hΓ A (.sort s₁) hA rfl
      have hsc : ∀ y ∈ A.fv, y ∈ Γ.names := Tm.fv_of_scoped A _ (by
        rw [hA, ← Ctx.length_toDB, hΔ]; exact hA'.scoped)
      have hz := freshFor_not_in (Γ.names ++ (Tm.lam x A b).fv ++ (Tm.pi y A₁ B₁).fv)
      generalize freshFor (Γ.names ++ (Tm.lam x A b).fv ++ (Tm.pi y A₁ B₁).fv) = z at hz
      have hzn : z ∉ Γ.names := fun e => hz (List.mem_append_left _ (List.mem_append_left _ e))
      have hzf : z ∉ (Tm.lam x A b).fv := fun e => hz (List.mem_append_left _
        (List.mem_append_right _ e))
      have hzT : z ∉ (Tm.pi y A₁ B₁).fv := fun e => hz (List.mem_append_right _ e)
      have hΓ' : Ctx.Wf sg ((z, A) :: Γ) := ⟨hΓ, hzn, hsc, s₁, dA⟩
      have hΔ' : Ctx.toDB ((z, A) :: Γ) = A' :: Δ := by simp [Ctx.toDB, hA, hΔ]
      have eB : (B₁.rename y z).toDB (Ctx.names ((z, A) :: Γ)) = B' := by
        simp only [Ctx.names_cons]
        rw [Tm.toDB_rename B₁ _ (fun e => hzT (by
          simp only [Tm.fv]; exact List.mem_append_right _ e)), hB₁]
      have db := ihb ((z, A) :: Γ) hΔ' hΓ' (b.rename x z) (B₁.rename y z) (by
        simp only [Ctx.names_cons]
        rw [Tm.toDB_rename b _ (fun e => hzf (by
          simp only [Tm.fv]; exact List.mem_append_right _ e)), hb]) eB
      have dB := ihB ((z, A) :: Γ) hΔ' hΓ' (B₁.rename y z) (.sort s₂) eB rfl
      refine .alpha (.lam dA hzn hzf db dB) ?_
      simp only [Tm.toDB, hA, hA₁]
      congr 1
      rw [hB₁]
      simpa using eB
  | @app Δ f' u' A' B' hf hu ihf ihu =>
      intro Γ hΔ hΓ t T ht hT
      obtain ⟨f, u, rfl, hf', hu'⟩ := Tm.toDB_eq_app ht
      have hΔw : DeBruijn.Wf sg Δ := hΔ ▸ hΓ.toDB
      have hsc : (DeBruijn.Tm.pi A' B').Scoped Γ.names.length := by
        rw [← Ctx.length_toDB, hΔ]; exact hf.scoped_type hΔw
      have hP := Tm.toDB_fromDB (N := N) _ _ hΓ.nodup hsc
      generalize hP' : fromDB Γ.names (DeBruijn.Tm.pi A' B') = P at hP
      obtain ⟨z, A₀, B₀, rfl, hA₀, hB₀⟩ := Tm.toDB_eq_pi hP
      have df := ihf Γ hΔ hΓ f (.pi z A₀ B₀) hf' (by simp [Tm.toDB, hA₀, hB₀])
      have du := ihu Γ hΔ hΓ u A₀ hu' hA₀
      refine .alpha (.app df du) ?_
      rw [Tm.toDB_inst, hB₀, hu', hT]
  | @conv Δ t' A'' B'' s ht' hB hc iht ihB =>
      intro Γ hΔ hΓ t T ht hT
      have hΔw : DeBruijn.Wf sg Δ := hΔ ▸ hΓ.toDB
      have hsc : A''.Scoped Γ.names.length := by
        rw [← Ctx.length_toDB, hΔ]; exact ht'.scoped_type hΔw
      have hP := Tm.toDB_fromDB (N := N) _ _ hΓ.nodup hsc
      have dt := iht Γ hΔ hΓ t (fromDB Γ.names A'') ht hP
      have dB := ihB Γ hΔ hΓ T (.sort s) hT rfl
      refine .conv dt dB ?_
      show DeBruijn.Conv _ _
      rw [hP, hT]
      exact hc
  | ind hi =>
      intro Γ _ _ t T ht hT
      rw [Tm.toDB_eq_ind ht, Tm.toDB_eq_sort hT]
      exact .ind hi
  | ctor hc hm hl hlen _ ih =>
      intro Γ hΔ hΓ t T ht hT
      obtain ⟨as, rfl, rfl⟩ := Tm.toDB_eq_ctor ht
      rw [Tm.toDB_eq_ind hT]
      rw [Tm.isList_toDB] at hl
      rw [Tm.toList_toDB, List.length_map] at hlen
      exact .ctor hc hm hl hlen
        (fun j hj A hA => ih j hj Γ hΔ hΓ _ A (Tm.nth_toDB _ _ _).symm hA)
  | elim hm _ hl hlen _ _ _ ihC ihb iha iht =>
      intro Γ hΔ hΓ t T ht hT
      obtain ⟨C, bs, t₀, rfl, rfl, rfl, rfl⟩ := Tm.toDB_eq_elim ht
      rw [Tm.isList_toDB] at hl
      rw [Tm.toList_toDB, List.length_map] at hlen
      exact .alpha (.elim hm (ihC Γ hΔ hΓ C _ rfl rfl) hl hlen
        (fun k c hc B hB => ihb k c hc Γ hΔ hΓ _ B (Tm.nth_toDB _ _ _).symm hB)
        (fun k c hc o ho A hA => iha k c hc o ho Γ hΔ hΓ A _ hA rfl)
        (iht Γ hΔ hΓ t₀ _ rfl rfl)) hT.symm

/-- **The named judgement is de Bruijn typing on translations**, in a valid context. -/
theorem hasType_iff_toDB {Γ : Ctx N} (hΓ : Ctx.Wf sg Γ) {t T : Tm N} :
    HasType sg Γ t T ↔ DeBruijn.HasType sg (Ctx.toDB Γ) (t.toDB Γ.names) (T.toDB Γ.names) :=
  ⟨fun h => h.toDB hΓ, fun h => HasType.ofDB h Γ rfl hΓ t T rfl rfl⟩

/-! ## What arrives from de Bruijn -/

/-- **Subject reduction.** -/
theorem HasType.preservation {Γ : Ctx N} {t t' T : Tm N} (h : HasType sg Γ t T) (hΓ : Ctx.Wf sg Γ)
    (hs : Step t t') : HasType sg Γ t' T :=
  (hasType_iff_toDB hΓ).mpr ((h.toDB hΓ).preservation hΓ.toDB (hs.toDB _))

/-- **Strong normalization**: every well-typed named term is strongly normalizing. -/
theorem HasType.sn {Γ : Ctx N} {t T : Tm N} (h : HasType sg Γ t T) (hsg : DeBruijn.WfSig sg)
    (hΓ : Ctx.Wf sg Γ) : SN Step t :=
  sn_of_toDB ((h.toDB hΓ).sn hsg hΓ.toDB)

/-- **Types are unique up to conversion.** -/
theorem HasType.unique {Γ : Ctx N} {t A B : Tm N} (hA : HasType sg Γ t A) (hB : HasType sg Γ t B)
    (hΓ : Ctx.Wf sg Γ) : Conv Γ A B :=
  (hA.toDB hΓ).unique (hB.toDB hΓ)

/-- **The judgement is decidable**: the de Bruijn checker, on translations. -/
def decHasType (hsg : DeBruijn.WfSig sg) (Γ : Ctx N) (hΓ : Ctx.Wf sg Γ) (t T : Tm N) :
    Decidable (HasType sg Γ t T) :=
  @decidable_of_iff _ _ (hasType_iff_toDB hΓ).symm
    (DeBruijn.decHasType hsg (Ctx.toDB Γ) hΓ.toDB (t.toDB Γ.names) (T.toDB Γ.names))

end LambdaLab.Languages.CoIC.Named
