import LambdaLab.Languages.CoC.DeBruijn.Classification

/-!
# CoC — strong normalization

Every well-typed term in a valid context is strongly normalizing (`HasType.sn`). The proof is
Girard's reducibility candidates, lifted to the dependent setting the way Geuvers does it ("A short
and flexible proof of strong normalization for the Calculus of Constructions", 1994): kinds are
interpreted through their **Fω skeletons**.

## Candidates

As for System F: a set of terms that contains only strongly normalizing terms (CR1), is closed
under reduction (CR2), and contains every neutral term all of whose reducts it contains (CR3).

## The semantic universe of a skeleton

A constructor of kind `K` is interpreted as an element of `KSem K.skel`: a candidate if the
skeleton is `*`, a function between such things if it is an arrow. So `λ X : * . X → X`, of kind
`* → *` (skeleton `* ⇒ *`), means a function from candidates to candidates. Products over
*types* vanish from the skeleton, and correspondingly a constructor's dependence on objects is
forgotten: `Vec n` is interpreted like `Vec` — types are SN regardless of the term they mention.

## Interpretation

`interp ξ t κ : KSem κ` interprets `t` at skeleton `κ`, given a valuation `ξ` with a semantic value
for each constructor variable (`none` for an object variable):

    interp ξ n κ          = ξ n, at κ
    interp ξ (Π A . B) *  = { M | ∀ N ∈ ⟦A⟧, ∀ α, M N ∈ ⟦B⟧(α . ξ) }   (α ranges over KSem A.skel
                                                                       when A is a kind, else
                                                                       there is no α)
    interp ξ (λ A . t) (a ⇒ b) = α ↦ interp (α . ξ) t b               (A a kind)
    interp ξ (λ A . t) κ  = interp (none . ξ) t κ                      (A a type)
    interp ξ (t u) κ      = interp ξ t (a ⇒ κ) (interp ξ u a)          (u a constructor of class a)
    interp ξ (t u) κ      = interp ξ t κ                               (u an object)

Which case of `t u` applies is decided by `cls` — syntactically, but in agreement with typing
(`HasType.cls_eq`). On ill-typed terms the interpretation is junk; every lemma about it takes a
typing derivation, which is what makes the junk unreachable.

`R ξ T = interp ξ T *` is the candidate of terms *realizing* `T`, for `T` a type or a kind; for
`*` and `□` it is all strongly normalizing terms.

## The lemmas, and the theorem

* `interp_ren` — interpretation commutes with renaming, unconditionally;
* `HasType.interp_subst` — and with a well-typed substitution, which the interpretation sees as
  the valuation of the substituted terms' interpretations: this is what makes a β-redex between
  constructors mean what its contractum means;
* `HasType.interp_step` — a well-typed reduction of a kind or constructor leaves its
  interpretation unchanged; hence convertible types have the same candidate (`interp_conv`), which
  is what the conversion rule needs;
* `HasType.fundamental` — if `Γ ⊢ M : T`, then `M[σ] ∈ R ξ T` whenever each variable's
  substitute realizes its type. With `σ` the identity, `M` is in a candidate, hence SN.
-/

namespace LambdaLab.Languages.CoC.DeBruijn

open LambdaLab (SN RTC)

/-! ## Strong normalization, structurally -/

/-- Not an abstraction: applying it creates no redex at the top. -/
def Tm.Neutral : Tm → Prop
  | .lam _ _ => False
  | _ => True

theorem sn_of_subst {σ : Nat → Tm} {t : Tm} (h : SN Step (t.subst σ)) : SN Step t := by
  generalize hx : t.subst σ = x at h
  induction h generalizing t with
  | intro _ ih => exact .intro (fun t' hs => ih _ (hx ▸ hs.subst σ) rfl)

theorem sn_app_left {t u : Tm} (h : SN Step (.app t u)) : SN Step t := by
  generalize hx : Tm.app t u = x at h
  induction h generalizing t with
  | intro _ ih => exact .intro (fun t' hs => ih _ (hx ▸ .appL hs) rfl)

theorem sn_pi {A B : Tm} (hA : SN Step A) (hB : SN Step B) : SN Step (.pi A B) := by
  induction hA generalizing B with
  | intro _ ihA =>
      induction hB with
      | intro hB' ihB =>
          refine .intro (fun w hw => ?_)
          cases hw with
          | piA h => exact ihA _ h (.intro hB')
          | piB h => exact ihB _ h

theorem sn_sort (s : Srt) : SN Step (.sort s) := .intro (fun _ h => absurd h Step.sort_inv)

/-! ## Candidates -/

/-- **A reducibility candidate.** -/
structure Cand where
  mem : Tm → Prop
  /-- CR1 -/
  sn : ∀ {t}, mem t → SN Step t
  /-- CR2 -/
  step : ∀ {t t'}, mem t → Step t t' → mem t'
  /-- CR3 -/
  neutral : ∀ {t}, t.Neutral → (∀ t', Step t t' → mem t') → mem t

/-- The strongly normalizing terms. -/
def snCand : Cand where
  mem t := SN Step t
  sn h := h
  step h s := h.unfold s
  neutral _ h := .intro h

instance : Inhabited Cand := ⟨snCand⟩

theorem Cand.var (C : Cand) (n : Nat) : C.mem (.var n) :=
  C.neutral trivial (fun _ s => absurd s Step.var_inv)

theorem Cand.red (C : Cand) {t t' : Tm} (h : C.mem t) (hr : Red t t') : C.mem t' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact C.step ih hs

private theorem Cand.beta_aux (C : Cand) : ∀ {A : Tm}, SN Step A → ∀ {t : Tm}, SN Step t →
    ∀ {u : Tm}, SN Step u → C.mem (t.inst u) → C.mem (.app (.lam A t) u) := by
  intro A hA
  induction hA with
  | @intro A hA ihA =>
      intro t ht
      induction ht with
      | @intro t ht iht =>
          intro u hu
          induction hu with
          | @intro u hu ihu =>
              intro h
              refine C.neutral trivial (fun w hw => ?_)
              cases hw with
              | beta => exact h
              | appL hs =>
                  cases hs with
                  | lamA hA' => exact ihA _ hA' (.intro ht) (.intro hu) h
                  | lamB ht' => exact iht _ ht' (.intro hu) (C.step h (ht'.subst _))
              | appR hu' => exact ihu _ hu' (C.red h (Red.inst .refl (RTC.single hu')))

/-- **Weak head expansion**: a β-redex is in a candidate if its contractum is and its annotation
and argument normalize. -/
theorem Cand.beta (C : Cand) {A t u : Tm} (hA : SN Step A) (hu : SN Step u)
    (h : C.mem (t.inst u)) : C.mem (.app (.lam A t) u) :=
  C.beta_aux hA (sn_of_subst (C.sn h)) hu h

/-- **The product candidate**: terms that, applied to anything in `X`, land in every `F i`. -/
def piCand (X : Cand) {I : Type} [Inhabited I] (F : I → Cand) : Cand where
  mem M := ∀ N, X.mem N → ∀ i, (F i).mem (.app M N)
  sn h := sn_app_left ((F default).sn (h _ (X.var 0) default))
  step h hs N hN i := (F i).step (h N hN i) (.appL hs)
  neutral := by
    intro M hn hM N hN i
    have key : ∀ N, SN Step N → X.mem N → (F i).mem (.app M N) := by
      intro N hsn
      induction hsn with
      | @intro N _ ih =>
          intro hN
          refine (F i).neutral trivial (fun w hw => ?_)
          cases hw with
          | beta => exact hn.elim
          | appL hs => exact hM _ hs N hN i
          | appR hs => exact ih _ hs (X.step hN hs)
    exact key N (X.sn hN) hN

/-! ## The semantic universe -/

/-- The meaning of a skeleton: candidates at `*`, functions at an arrow. -/
def KSem : SK → Type
  | .star => Cand
  | .arr a b => KSem a → KSem b

def KSem.default : (κ : SK) → KSem κ
  | .star => snCand
  | .arr _ b => fun _ => KSem.default b

instance (κ : SK) : Inhabited (KSem κ) := ⟨KSem.default κ⟩

/-- A semantic value together with its skeleton. -/
structure SVal where
  κ : SK
  v : KSem κ

/-- Read a semantic value at a skeleton — the value itself if the skeletons agree, junk if not. -/
def SVal.at (x : SVal) (κ : SK) : KSem κ :=
  if h : x.κ = κ then h ▸ x.v else KSem.default κ

theorem SVal.at_self (x : SVal) : x.at x.κ = x.v := by simp [SVal.at]

theorem SVal.eta (x : SVal) : (⟨x.κ, x.at x.κ⟩ : SVal) = x := by rw [SVal.at_self]

/-- A valuation: a semantic value for each constructor variable, `none` for an object
variable. -/
abbrev Val := Nat → Option SVal

/-- The class of each variable, as the valuation has it. -/
def Val.shape (ξ : Val) : Nat → Option SK := fun n => (ξ n).map SVal.κ

theorem Val.shape_scons (e : Option SVal) (ξ : Val) :
    Val.shape (scons e ξ) = scons (e.map SVal.κ) ξ.shape := by
  funext n; cases n <;> rfl

/-- A product kind's skeleton over a kind is an arrow… -/
theorem Tm.skel_pi_dep {A B : Tm} (hB : B.isKind = true) (hA : A.isKind = true) :
    (Tm.pi A B).skel = .arr A.skel B.skel := by simp [Tm.skel, hA, hB]

/-- …and over a type, the codomain's skeleton. -/
theorem Tm.skel_pi_obj {A B : Tm} (hB : B.isKind = true) (hA : A.isKind = false) :
    (Tm.pi A B).skel = B.skel := by simp [Tm.skel, hA, hB]

/-! ## Interpretation -/

/-- **The interpretation of a term at a skeleton.** -/
def interp : Val → Tm → (κ : SK) → KSem κ
  | ξ, .var n, κ =>
      match ξ n with
      | some x => x.at κ
      | none => KSem.default κ
  | _, .sort _, κ => KSem.default κ
  | ξ, .pi A B, .star =>
      if A.isKind then
        piCand (interp ξ A .star) (I := KSem A.skel)
          (fun x => interp (scons (some ⟨A.skel, x⟩) ξ) B .star)
      else piCand (interp ξ A .star) (I := Unit) (fun _ => interp (scons none ξ) B .star)
  | _, .pi _ _, .arr a b => KSem.default (.arr a b)
  | ξ, .lam A t, κ =>
      if A.isKind then
        match κ with
        | .arr a b => fun x => interp (scons (some ⟨a, x⟩) ξ) t b
        | .star => KSem.default .star
      else interp (scons none ξ) t κ
  | ξ, .app t u, κ =>
      match cls ξ.shape u with
      | some a => interp ξ t (.arr a κ) (interp ξ u a)
      | none => interp ξ t κ

/-- **The realizers of a type or kind.** -/
abbrev R (ξ : Val) (T : Tm) : Cand := interp ξ T .star

/-! ## Renaming -/

/-- **Interpretation commutes with renaming.** -/
theorem interp_ren : ∀ (t : Tm) (ξ : Val) (r : Nat → Nat) (κ : SK),
    interp ξ (t.ren r) κ = interp (ξ ∘ r) t κ
  | .var _, _, _, _ => rfl
  | .sort _, _, _, _ => rfl
  | .pi A B, ξ, r, κ => by
      have e : ∀ x : Option SVal, scons x ξ ∘ upRen r = scons x (ξ ∘ r) := fun x => by
        funext n; cases n <;> rfl
      cases κ with
      | arr a b => rfl
      | star =>
          simp only [Tm.ren, interp, Tm.isKind_ren, interp_ren A, interp_ren B, e]
          rw [Tm.skel_ren]
  | .lam A t, ξ, r, κ => by
      have e : ∀ x : Option SVal, scons x ξ ∘ upRen r = scons x (ξ ∘ r) := fun x => by
        funext n; cases n <;> rfl
      simp only [Tm.ren, interp, Tm.isKind_ren]
      cases A.isKind with
      | false => simp only [interp_ren t, e]
      | true =>
          cases κ with
          | star => rfl
          | arr a b => simp only [interp_ren t, e]
  | .app t u, ξ, r, κ => by
      have hs : Val.shape ξ ∘ r = Val.shape (ξ ∘ r) := rfl
      simp only [Tm.ren, interp, cls_ren, hs]
      cases cls (Val.shape (ξ ∘ r)) u with
      | none => simp only [interp_ren t]
      | some a => simp only [interp_ren t, interp_ren u]

theorem interp_shift (t : Tm) (e : Option SVal) (ξ : Val) (κ : SK) :
    interp (scons e ξ) t.shift κ = interp ξ t κ := by
  rw [Tm.shift, interp_ren]
  rfl

/-! ## Substitution -/

/-- The valuation a substitution induces: each variable of class `a` gets the interpretation of
its substitute at `a`. -/
def semSubst (ξ : Val) (σ : Nat → Tm) (ρ : Nat → Option SK) : Val :=
  fun n => (ρ n).map (fun a => ⟨a, interp ξ (σ n) a⟩)

theorem semSubst_shape (ξ : Val) (σ : Nat → Tm) (ρ : Nat → Option SK) :
    (semSubst ξ σ ρ).shape = ρ := by
  funext n
  simp only [Val.shape, semSubst, Option.map_map]
  cases ρ n <;> rfl

/-- Lifting a substitution under a binder lifts its valuation. -/
theorem semSubst_up (e : Option SVal) (ξ : Val) (σ : Nat → Tm) (ρ : Nat → Option SK) :
    semSubst (scons e ξ) (Tm.up σ) (scons (e.map SVal.κ) ρ) = scons e (semSubst ξ σ ρ) := by
  funext n
  cases n with
  | zero =>
      cases e with
      | none => rfl
      | some x =>
          simp only [semSubst, scons_zero, Option.map_some, Tm.up_zero, interp]
          rw [SVal.eta]
  | succ n =>
      simp only [semSubst, scons_succ, Tm.up_succ]
      congr 1
      funext a
      rw [show (σ n).ren Nat.succ = (σ n).shift from rfl, interp_shift]

/-- The valuation of a single instantiation. -/
theorem semSubst_inst {ξ : Val} {ρ : Nat → Option SK} (hξ : ξ.shape = ρ) (u : Tm)
    (c : Option SK) :
    semSubst ξ (scons u Tm.var) (scons c ρ) = scons (c.map fun a => ⟨a, interp ξ u a⟩) ξ := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [semSubst, scons_succ, ← hξ, Val.shape]
      cases h : ξ n with
      | none => rfl
      | some x =>
          simp only [Option.map_some, interp, h]
          rw [SVal.eta]

/-- A kind or constructor: typed by `□`, or by something `□` types. -/
def KindOrCon (Γ : Ctx) (T : Tm) : Prop := T = .sort .box ∨ HasType Γ T (.sort .box)

theorem KindOrCon.sort (Γ : Ctx) (s : Srt) : KindOrCon Γ (.sort s) := by
  cases s with
  | star => exact .inr .sort
  | box => exact .inl rfl

/-- A kind-or-constructor that is typed is typed by `□`. -/
theorem KindOrCon.box {Γ : Ctx} {T : Tm} {s : Srt} (h : KindOrCon Γ T)
    (hT : HasType Γ T (.sort s)) : HasType Γ T (.sort .box) := by
  rcases h with h | h
  · subst h; exact (hT.ne_box rfl).elim
  · exact h

/-- **Interpretation commutes with a well-typed substitution.** -/
theorem HasType.interp_subst {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hT : KindOrCon Γ T) {Δ : Ctx} {σ : Nat → Tm} {ξ : Val} (hΔ : Wf Δ) (hσ : SubstOk σ Γ Δ)
    (hk : ∀ n, (σ n).isKind = false) (hξ : ξ.shape = Δ.shape) :
    interp ξ (t.subst σ) T.skel = interp (semSubst ξ σ Γ.shape) t T.skel := by
  induction h generalizing Δ σ ξ with
  | sort => rfl
  | @var Γ n A hn =>
      obtain ⟨s, hs⟩ := hΓ.lookup hn
      have hAk : A.isKind = true := (hs.isKind_iff hΓ).mpr (by
        rcases hT with h | h
        · subst h; exact (hs.ne_box rfl).elim
        · exact (hs.unique h).sort_inj ▸ rfl)
      simp only [Tm.subst, interp, semSubst, Ctx.shape, hn, hAk, if_true, Option.map_some]
      rw [SVal.at_self]
  | @pi Γ A B s₁ s₂ hA hB ihA ihB =>
      have hA' := ihA hΓ (KindOrCon.sort Γ s₁) hΔ hσ hk hξ
      simp only [Tm.skel] at hA' ⊢
      simp only [Tm.subst, interp, Tm.isKind_subst hk, hA']
      rw [Tm.skel_subst hk]
      cases hAk : A.isKind with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          have := ihB (hΓ.cons hA) (KindOrCon.sort _ s₂) (σ := Tm.up σ) (ξ := scons none ξ)
            (hΔ.cons (hA.subst hσ)) (hσ.up A) (Tm.up_not_kind hk)
            (by rw [Val.shape_scons, hξ, Ctx.shape_cons]; simp [Tm.cls₀, Tm.isKind_subst hk, hAk])
          simp only [Tm.skel] at this
          rw [this, Ctx.shape_cons, show A.cls₀ = (none : Option SVal).map SVal.κ by
            simp [Tm.cls₀, hAk], semSubst_up]
      | true =>
          simp only [if_true]
          congr 1
          funext x
          have := ihB (hΓ.cons hA) (KindOrCon.sort _ s₂) (σ := Tm.up σ)
            (ξ := scons (some ⟨A.skel, x⟩) ξ) (hΔ.cons (hA.subst hσ)) (hσ.up A)
            (Tm.up_not_kind hk)
            (by rw [Val.shape_scons, hξ, Ctx.shape_cons]
                simp [Tm.cls₀, Tm.isKind_subst hk, Tm.skel_subst hk, hAk])
          simp only [Tm.skel] at this
          rw [this, Ctx.shape_cons, show A.cls₀ = (some (⟨A.skel, x⟩ : SVal)).map SVal.κ by
            simp [Tm.cls₀, hAk], semSubst_up]
  | @lam Γ A t B s₁ s₂ hA ht hB _ iht _ =>
      have hBk : B.isKind = true := by
        rcases hT with h | h
        · cases h
        · have := h.isKind_of_box hΓ rfl
          simpa [Tm.isKind] using this
      have hs₂ : s₂ = .box := (hB.sort_box_iff (hΓ.cons hA)).mpr hBk
      subst hs₂
      have hΓ' := hΓ.cons hA
      have hΔ' := hΔ.cons (hA.subst hσ)
      cases hAk : A.isKind with
      | false =>
          rw [Tm.skel_pi_obj hBk hAk]
          have := iht hΓ' (.inr hB) (σ := Tm.up σ) (ξ := scons none ξ) hΔ' (hσ.up A)
            (Tm.up_not_kind hk)
            (by rw [Val.shape_scons, hξ, Ctx.shape_cons]; simp [Tm.cls₀, Tm.isKind_subst hk, hAk])
          rw [Ctx.shape_cons, show A.cls₀ = (none : Option SVal).map SVal.κ by
            simp [Tm.cls₀, hAk], semSubst_up] at this
          simp only [Tm.subst, interp, Tm.isKind_subst hk, hAk, Bool.false_eq_true, if_false]
          exact this
      | true =>
          rw [Tm.skel_pi_dep hBk hAk]
          simp only [Tm.subst, interp, Tm.isKind_subst hk, hAk, if_true]
          funext x
          have := iht hΓ' (.inr hB) (σ := Tm.up σ) (ξ := scons (some ⟨A.skel, x⟩) ξ) hΔ'
            (hσ.up A) (Tm.up_not_kind hk)
            (by rw [Val.shape_scons, hξ, Ctx.shape_cons]
                simp [Tm.cls₀, Tm.isKind_subst hk, Tm.skel_subst hk, hAk])
          rw [Ctx.shape_cons, show A.cls₀ = (some (⟨A.skel, x⟩ : SVal)).map SVal.κ by
            simp [Tm.cls₀, hAk], semSubst_up] at this
          exact this
  | @app Γ t u A B ht hu iht ihu =>
      obtain ⟨s, hs⟩ := (ht.correct hΓ).resolve_left (by intro e; cases e)
      obtain ⟨s₁, s₂, hA, hB, hc⟩ := hs.gen_pi
      have huk : u.isKind = false := hu.not_kind_of_sorted hA hΓ
      have hTk : (B.inst u).isKind = true := by
        rcases hT with h | h
        · obtain ⟨s', hs'⟩ := ht.inst_sorted hu hΓ
          rw [h] at hs'
          exact (hs'.ne_box rfl).elim
        · exact h.isKind_of_box hΓ rfl
      have hBk : B.isKind = true := by
        rwa [Tm.inst, Tm.isKind_subst (Tm.scons_not_kind huk)] at hTk
      have hpi : HasType Γ (.pi A B) (.sort .box) := by
        have : s = .box := (hs.sort_box_iff hΓ).mpr (by simpa [Tm.isKind] using hBk)
        rwa [this] at hs
      have hsk : (B.inst u).skel = B.skel := by
        rw [Tm.inst, Tm.skel_subst (Tm.scons_not_kind huk)]
      rw [hsk]
      have hu' : cls Δ.shape (u.subst σ) = A.cls₀ := by
        rw [(hu.subst hσ).cls_eq hΔ (fun e => (hA.subst hσ).ne_box e)]
        simp [Tm.cls₀, Tm.isKind_subst hk, Tm.skel_subst hk]
      have hu'' : cls Γ.shape u = A.cls₀ := hu.cls_eq hΓ (fun e => hA.ne_box e)
      have iht' := iht hΓ (.inr hpi) hΔ hσ hk hξ
      simp only [Tm.subst, interp, hξ, hu', semSubst_shape, hu'']
      cases hAk : A.isKind with
      | false =>
          rw [Tm.skel_pi_obj hBk hAk] at iht'
          simp only [Tm.cls₀, hAk, Bool.false_eq_true, if_false]
          exact iht'
      | true =>
          rw [Tm.skel_pi_dep hBk hAk] at iht'
          simp only [Tm.cls₀, hAk, if_true]
          have hs₁ : s₁ = .box := (hA.sort_box_iff hΓ).mpr hAk
          subst hs₁
          rw [iht', ihu hΓ (.inr hA) hΔ hσ hk hξ]
  | @conv Γ t A B s ht hB hc iht _ =>
      have hB' := hT.box hB
      have hA : A ≠ .sort .box := fun e => by subst e; exact hB.conv_box_eq hΓ hc
      obtain ⟨s', hs'⟩ := (ht.correct hΓ).resolve_left hA
      obtain ⟨hss, hsk⟩ := hs'.kind_conv hB' hΓ hc
      subst hss
      rw [← hsk rfl]
      exact iht hΓ (.inr hs') hΔ hσ hk hξ

/-! ## Reduction -/

/-- **A well-typed reduction of a kind or constructor does not change its interpretation.** -/
theorem HasType.interp_step {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hT : KindOrCon Γ T) {ξ : Val} (hξ : ξ.shape = Γ.shape) {t' : Tm} (hs : Step t t') :
    interp ξ t T.skel = interp ξ t' T.skel := by
  induction h generalizing ξ t' with
  | sort => cases hs
  | var => cases hs
  | @pi Γ A B s₁ s₂ hA hB ihA ihB =>
      simp only [Tm.skel]
      cases hs with
      | @piA _ A' _ h' =>
          have hk := hA.isKind_step hΓ h'
          have hA' := ihA hΓ (KindOrCon.sort Γ s₁) hξ h'
          simp only [Tm.skel] at hA'
          simp only [interp, hk, hA']
          cases hAk : A.isKind with
          | false => rfl
          | true =>
              have hs₁ : s₁ = .box := (hA.sort_box_iff hΓ).mpr hAk
              subst hs₁
              rw [hA.skel_step hΓ h']
      | @piB _ _ B' h' =>
          simp only [interp]
          cases hAk : A.isKind with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              have := ihB (hΓ.cons hA) (KindOrCon.sort _ s₂) (ξ := scons none ξ)
                (by rw [Val.shape_scons, hξ, Ctx.shape_cons]; simp [Tm.cls₀, hAk]) h'
              simp only [Tm.skel] at this
              rw [this]
          | true =>
              simp only [if_true]
              congr 1
              funext x
              have := ihB (hΓ.cons hA) (KindOrCon.sort _ s₂) (ξ := scons (some ⟨A.skel, x⟩) ξ)
                (by rw [Val.shape_scons, hξ, Ctx.shape_cons]; simp [Tm.cls₀, hAk]) h'
              simp only [Tm.skel] at this
              exact this
  | @lam Γ A t B s₁ s₂ hA ht hB _ iht _ =>
      have hBk : B.isKind = true := by
        rcases hT with h | h
        · cases h
        · have := h.isKind_of_box hΓ rfl
          simpa [Tm.isKind] using this
      have hs₂ : s₂ = .box := (hB.sort_box_iff (hΓ.cons hA)).mpr hBk
      subst hs₂
      cases hAk : A.isKind with
      | false =>
          rw [Tm.skel_pi_obj hBk hAk]
          cases hs with
          | @lamA _ A' _ h' =>
              have hk := hA.isKind_step hΓ h'
              simp only [interp, hk, hAk]
          | @lamB _ _ t' h' =>
              simp only [interp, hAk, Bool.false_eq_true, if_false]
              exact iht (hΓ.cons hA) (.inr hB) (ξ := scons none ξ)
                (by rw [Val.shape_scons, hξ, Ctx.shape_cons]; simp [Tm.cls₀, hAk]) h'
      | true =>
          rw [Tm.skel_pi_dep hBk hAk]
          cases hs with
          | @lamA _ A' _ h' =>
              have hk := hA.isKind_step hΓ h'
              simp only [interp, hk, hAk]
          | @lamB _ _ t' h' =>
              simp only [interp, hAk, if_true]
              funext x
              exact iht (hΓ.cons hA) (.inr hB) (ξ := scons (some ⟨A.skel, x⟩) ξ)
                (by rw [Val.shape_scons, hξ, Ctx.shape_cons]; simp [Tm.cls₀, hAk]) h'
  | @app Γ t u A B ht hu iht ihu =>
      obtain ⟨s, hs'⟩ := (ht.correct hΓ).resolve_left (by intro e; cases e)
      obtain ⟨s₁, s₂, hA, hB, _⟩ := hs'.gen_pi
      have huk : u.isKind = false := hu.not_kind_of_sorted hA hΓ
      have hTk : (B.inst u).isKind = true := by
        rcases hT with h | h
        · obtain ⟨s', hs''⟩ := ht.inst_sorted hu hΓ
          rw [h] at hs''
          exact (hs''.ne_box rfl).elim
        · exact h.isKind_of_box hΓ rfl
      have hBk : B.isKind = true := by
        rwa [Tm.inst, Tm.isKind_subst (Tm.scons_not_kind huk)] at hTk
      have hpi : HasType Γ (.pi A B) (.sort .box) := by
        have : s = .box := (hs'.sort_box_iff hΓ).mpr (by simpa [Tm.isKind] using hBk)
        rwa [this] at hs'
      have hsk : (B.inst u).skel = B.skel := by
        rw [Tm.inst, Tm.skel_subst (Tm.scons_not_kind huk)]
      rw [hsk]
      have hu'' : cls Γ.shape u = A.cls₀ := hu.cls_eq hΓ (fun e => hA.ne_box e)
      cases hs with
      | @appL _ t' _ h' =>
          have iht' := iht hΓ (.inr hpi) hξ h'
          simp only [interp, hξ, hu'']
          cases hAk : A.isKind with
          | false =>
              rw [Tm.skel_pi_obj hBk hAk] at iht'
              simp only [Tm.cls₀, hAk, Bool.false_eq_true, if_false]
              exact iht'
          | true =>
              rw [Tm.skel_pi_dep hBk hAk] at iht'
              simp only [Tm.cls₀, hAk, if_true]
              rw [iht']
      | @appR _ _ u' h' =>
          have hu''' : cls Γ.shape u' = A.cls₀ :=
            (hu.preservation hΓ h').cls_eq hΓ (fun e => hA.ne_box e)
          simp only [interp, hξ, hu'', hu''']
          cases hAk : A.isKind with
          | false => simp only [Tm.cls₀, hAk, Bool.false_eq_true, if_false]
          | true =>
              simp only [Tm.cls₀, hAk, if_true]
              have hs₁ : s₁ = .box := (hA.sort_box_iff hΓ).mpr hAk
              subst hs₁
              rw [ihu hΓ (.inr hA) hξ h']
      | @beta A₀ b _ =>
          obtain ⟨B₀, s₁', s₂', hA₀, hb, hB₀, hc⟩ := ht.gen_lam
          obtain ⟨hAA, hBB⟩ := Conv.pi_inj hc
          obtain ⟨hss₁, hsk₁⟩ := hA₀.kind_conv hA hΓ hAA
          subst hss₁
          have hΓ₀ := hΓ.cons hA₀
          have hB' : HasType (A₀ :: Γ) B (.sort s₂) := hB.ctx_conv hA hAA.symm
          obtain ⟨hss₂, hsk₂⟩ := hB₀.kind_conv hB' hΓ₀ hBB
          subst hss₂
          have hs₂ : s₂' = .box := (hB'.sort_box_iff hΓ₀).mpr hBk
          subst hs₂
          have hk₀ : A₀.isKind = A.isKind := by
            cases s₁' with
            | box => rw [(hA₀.sort_box_iff hΓ).mp rfl, (hA.sort_box_iff hΓ).mp rfl]
            | star => rw [hA₀.not_kind_of_sorted .sort hΓ, hA.not_kind_of_sorted .sort hΓ]
          have hsub := hb.interp_subst hΓ₀ (.inr hB₀) hΓ (σ := scons u Tm.var) (ξ := ξ)
            (fun n C hC => by
              cases n with
              | zero =>
                  simp only [Ctx.lookup_zero, Option.some.injEq] at hC
                  subst hC
                  rw [show A₀.shift.subst (scons u Tm.var) = A₀ from Tm.shift_inst A₀ u]
                  exact .conv hu hA₀ hAA.symm
              | succ n =>
                  simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hC
                  obtain ⟨C', hC', rfl⟩ := hC
                  rw [show C'.shift.subst (scons u Tm.var) = C' from Tm.shift_inst C' u]
                  exact .var hC')
            (Tm.scons_not_kind huk) hξ
          rw [hsk₂ rfl] at hsub
          rw [show (b.inst u) = b.subst (scons u Tm.var) from rfl, hsub, Ctx.shape_cons,
            semSubst_inst hξ]
          simp only [interp, hξ, hu'', hk₀]
          cases hAk : A.isKind with
          | false => simp [Tm.cls₀, hAk, hk₀]
          | true =>
              have hs₁ : s₁' = .box := (hA₀.sort_box_iff hΓ).mpr (hk₀ ▸ hAk)
              subst hs₁
              simp [Tm.cls₀, hAk, hk₀, hsk₁ rfl]
  | @conv Γ t A B s ht hB hc iht _ =>
      have hB' := hT.box hB
      have hA : A ≠ .sort .box := fun e => by subst e; exact hB.conv_box_eq hΓ hc
      obtain ⟨s', hs'⟩ := (ht.correct hΓ).resolve_left hA
      obtain ⟨hss, hsk⟩ := hs'.kind_conv hB' hΓ hc
      subst hss
      rw [← hsk rfl]
      exact iht hΓ (.inr hs') hξ hs

theorem HasType.interp_red {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ)
    (hT : KindOrCon Γ T) {ξ : Val} (hξ : ξ.shape = Γ.shape) {t' : Tm} (hr : Red t t') :
    interp ξ t T.skel = interp ξ t' T.skel := by
  induction hr with
  | refl => rfl
  | tail hr hs ih => exact ih.trans ((h.preservation_red hΓ hr).interp_step hΓ hT hξ hs)

/-- **Convertible types have the same realizers.** -/
theorem HasType.interp_conv {Γ : Ctx} {A B : Tm} {s s' : Srt} (hA : HasType Γ A (.sort s))
    (hB : HasType Γ B (.sort s')) (hΓ : Wf Γ) (hc : Conv A B) {ξ : Val}
    (hξ : ξ.shape = Γ.shape) : R ξ A = R ξ B := by
  obtain ⟨C, hAC, hBC⟩ := hc
  have e1 := hA.interp_red hΓ (KindOrCon.sort Γ s) hξ hAC
  have e2 := hB.interp_red hΓ (KindOrCon.sort Γ s') hξ hBC
  simp only [Tm.skel] at e1 e2
  exact e1.trans e2.symm

/-! ## The fundamental theorem -/

/-- **Every well-typed term realizes its type**, under any substitution of realizers. -/
theorem HasType.fundamental {Γ : Ctx} {M T : Tm} (h : HasType Γ M T) (hΓ : Wf Γ) {ξ : Val}
    {σ : Nat → Tm} (hξ : ξ.shape = Γ.shape)
    (hσ : ∀ n A, Γ.lookup n = some A → (R ξ A).mem (σ n)) : (R ξ T).mem (M.subst σ) := by
  induction h generalizing ξ σ with
  | sort => exact sn_sort _
  | var hn => exact hσ _ _ hn
  | @pi Γ A B s₁ s₂ hA hB ihA ihB =>
      have hsA : SN Step (A.subst σ) := ihA hΓ hξ hσ
      let e : Option SVal := A.cls₀.map fun a => ⟨a, default⟩
      have he : e.map SVal.κ = A.cls₀ := by
        simp only [e, Option.map_map]
        cases A.cls₀ <;> rfl
      have hsB : SN Step (B.subst (scons (.var 0) σ)) :=
        ihB (hΓ.cons hA) (ξ := scons e ξ)
          (by rw [Val.shape_scons, hξ, Ctx.shape_cons, he])
          (fun n C hC => by
            cases n with
            | zero =>
                simp only [Ctx.lookup_zero, Option.some.injEq] at hC
                subst hC
                show (interp (scons e ξ) A.shift .star).mem _
                rw [interp_shift]
                exact Cand.var _ 0
            | succ n =>
                simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hC
                obtain ⟨C', hC', rfl⟩ := hC
                show (interp (scons e ξ) C'.shift .star).mem _
                rw [interp_shift]
                exact hσ n C' hC')
      rw [← Tm.up_inst] at hsB
      exact sn_pi hsA (sn_of_subst hsB)
  | @lam Γ A t B s₁ s₂ hA ht hB ihA iht _ =>
      have hsA : SN Step (A.subst σ) := ihA hΓ hξ hσ
      have key : ∀ (e : Option SVal), e.map SVal.κ = A.cls₀ → ∀ N, (R ξ A).mem N →
          (R (scons e ξ) B).mem (.app ((Tm.lam A t).subst σ) N) := by
        intro e he N hN
        refine Cand.beta _ hsA ((R ξ A).sn hN) ?_
        rw [Tm.up_inst]
        exact iht (hΓ.cons hA) (ξ := scons e ξ)
          (by rw [Val.shape_scons, hξ, Ctx.shape_cons, he])
          (fun n C hC => by
            cases n with
            | zero =>
                simp only [Ctx.lookup_zero, Option.some.injEq] at hC
                subst hC
                show (interp (scons e ξ) A.shift .star).mem _
                rw [interp_shift]
                exact hN
            | succ n =>
                simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hC
                obtain ⟨C', hC', rfl⟩ := hC
                show (interp (scons e ξ) C'.shift .star).mem _
                rw [interp_shift]
                exact hσ n C' hC')
      show (interp ξ (.pi A B) .star).mem _
      simp only [interp]
      cases hAk : A.isKind with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          intro N hN _
          exact key none (by simp [Tm.cls₀, hAk]) N hN
      | true =>
          simp only [if_true]
          intro N hN x
          exact key (some ⟨A.skel, x⟩) (by simp [Tm.cls₀, hAk]) N hN
  | @app Γ t u A B ht hu iht ihu =>
      obtain ⟨s, hs⟩ := (ht.correct hΓ).resolve_left (by intro e; cases e)
      obtain ⟨s₁, s₂, hA, hB, _⟩ := hs.gen_pi
      have huk : u.isKind = false := hu.not_kind_of_sorted hA hΓ
      have hft := iht hΓ hξ hσ
      have hfu := ihu hΓ hξ hσ
      -- the result type's realizers are `B`'s, with `u`'s meaning for the bound variable
      have hsub := hB.interp_subst (hΓ.cons hA) (KindOrCon.sort _ s₂) hΓ (σ := scons u Tm.var)
        (ξ := ξ)
        (fun n C hC => by
          cases n with
          | zero =>
              simp only [Ctx.lookup_zero, Option.some.injEq] at hC
              subst hC
              rw [show A.shift.subst (scons u Tm.var) = A from Tm.shift_inst A u]
              exact hu
          | succ n =>
              simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hC
              obtain ⟨C', hC', rfl⟩ := hC
              rw [show C'.shift.subst (scons u Tm.var) = C' from Tm.shift_inst C' u]
              exact .var hC')
        (Tm.scons_not_kind huk) hξ
      simp only [Tm.skel] at hsub
      rw [Ctx.shape_cons, semSubst_inst hξ] at hsub
      show (interp ξ (B.inst u) .star).mem (.app (t.subst σ) (u.subst σ))
      rw [show B.inst u = B.subst (scons u Tm.var) from rfl, hsub]
      change (interp ξ (.pi A B) .star).mem (t.subst σ) at hft
      simp only [interp] at hft
      cases hAk : A.isKind with
      | false =>
          simp only [hAk, Bool.false_eq_true, if_false] at hft
          simpa [Tm.cls₀, hAk] using hft _ hfu ()
      | true =>
          simp only [hAk, if_true] at hft
          simpa [Tm.cls₀, hAk] using hft _ hfu (interp ξ u A.skel)
  | @conv Γ t A B s ht hB hc iht _ =>
      have hA : A ≠ .sort .box := fun e => by subst e; exact hB.conv_box_eq hΓ hc
      obtain ⟨s', hs'⟩ := (ht.correct hΓ).resolve_left hA
      rw [← hs'.interp_conv hB hΓ hc hξ]
      exact iht hΓ hξ hσ

/-! ## Strong normalization -/

/-- **Strong normalization**: every well-typed term in a valid context is strongly
normalizing. -/
theorem HasType.sn {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) : SN Step t := by
  let ξ : Val := fun n => (Γ.shape n).map fun a => ⟨a, default⟩
  have hξ : ξ.shape = Γ.shape := by
    funext n
    simp only [Val.shape, ξ, Option.map_map]
    cases Γ.shape n <;> rfl
  have := h.fundamental hΓ hξ (σ := Tm.var) (fun n _ _ => Cand.var _ n)
  rw [Tm.subst_var] at this
  exact (R ξ T).sn this

/-- Every type is strongly normalizing too — `□` trivially, anything else by being typed. -/
theorem HasType.sn_type {Γ : Ctx} {t T : Tm} (h : HasType Γ t T) (hΓ : Wf Γ) : SN Step T := by
  rcases h.correct hΓ with e | ⟨s, hs⟩
  · subst e; exact sn_sort _
  · exact hs.sn hΓ

end LambdaLab.Languages.CoC.DeBruijn
