import LambdaLab.Languages.CoIC.DeBruijn.Classification
import LambdaLab.Languages.CoIC.DeBruijn.Scope

/-!
# CoC with inductive types — strong normalization

Every well-typed term in a valid context over a valid signature is strongly normalizing
(`HasType.sn`). The proof is CoC's (`Languages/CoC/DeBruijn/Normalization.lean`) — Girard's
reducibility candidates, with kinds interpreted through their Fω skeletons, after Geuvers — plus a
candidate for each inductive type.

## Candidates

A set of terms that contains only strongly normalizing terms (CR1), is closed under reduction
(CR2), and contains every neutral term all of whose reducts it contains (CR3). *Neutral* now
excludes constructors as well as abstractions: a constructor can create a redex when eliminated.

## Interpretation

`interp ιc ξ t κ : KSem κ` interprets `t` at skeleton `κ`, given a candidate `ιc i` for each
inductive type and a valuation `ξ` with a semantic value for each constructor variable:

    interp ξ n κ          = ξ n, at κ
    interp ξ (Π A . B) *  = { M | ∀ N ∈ ⟦A⟧, ∀ α, M N ∈ ⟦B⟧(α . ξ) }
    interp ξ (λ A . t) (a ⇒ b) = α ↦ interp (α . ξ) t b            (A a kind)
    interp ξ (λ A . t) κ  = interp (none . ξ) t κ                   (A a type)
    interp ξ (t u) κ      = interp ξ t (a ⇒ κ) (interp ξ u a)       (u a constructor of class a)
    interp ξ (t u) κ      = interp ξ t κ                            (u an object)
    interp ξ (Ind i) *    = ιc i

`R ιc ξ T = interp ιc ξ T *` is the candidate of terms *realizing* `T`.

## The candidate of an inductive type

`IndMem` is the least set of strongly normalizing terms each of whose constructor reducts has
the constructor's shape, its recursive arguments in the set itself and its other arguments in
their types' candidates — a Lean inductive predicate, the recursive premise being strictly
positive. It is a candidate (`indCand`). Since an argument type mentions only earlier inductive
types (`WfSig`), the candidates are built along the signature (`sigCands`), each from those before
it, and an argument type means the same to the full assignment as to the partial one it was built
with (`R_arg_eq`, from `interp_congr`: the interpretation sees only what a term mentions).

## The theorem

* a constructor applied to realizers of its argument types is in the candidate (`IndMem.ctor`);
* the recursor applied to a member of the candidate, with branches realizing their types, realizes
  the motive (`elim_mem`) — by induction on the membership, which supplies the recursive calls,
  then on the normalization of the parts;
* everything else is CoC's proof: `HasType.fundamental` says `M[σ] ∈ R ξ T` when `Γ ⊢ M : T`, and
  with `σ` the identity, `M` is in a candidate, hence SN.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

variable {sg : Sig}

open LambdaLab (SN RTC)

/-! ## Strong normalization, structurally -/

/-- Neither an abstraction nor a constructor: applying it, or eliminating it, creates no redex
at the top. -/
def Tm.Neutral : Tm → Prop
  | .lam _ _ => False
  | .ctor _ _ _ _ => False
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
def interp (ιc : Nat → Cand) : Val → Tm → (κ : SK) → KSem κ
  | ξ, .var n, κ =>
      match ξ n with
      | some x => x.at κ
      | none => KSem.default κ
  | _, .sort _, κ => KSem.default κ
  | ξ, .pi A B, .star =>
      if A.isKind then
        piCand (interp ιc ξ A .star) (I := KSem A.skel)
          (fun x => interp ιc (scons (some ⟨A.skel, x⟩) ξ) B .star)
      else piCand (interp ιc ξ A .star) (I := Unit) (fun _ => interp ιc (scons none ξ) B .star)
  | _, .pi _ _, .arr a b => KSem.default (.arr a b)
  | ξ, .lam A t, κ =>
      if A.isKind then
        match κ with
        | .arr a b => fun x => interp ιc (scons (some ⟨a, x⟩) ξ) t b
        | .star => KSem.default .star
      else interp ιc (scons none ξ) t κ
  | ξ, .app t u, κ =>
      match cls ξ.shape u with
      | some a => interp ιc ξ t (.arr a κ) (interp ιc ξ u a)
      | none => interp ιc ξ t κ
  | _, .ind i, .star => ιc i
  | _, .ind _, .arr a b => KSem.default (.arr a b)
  | _, .ctor _ _ _ _, κ => KSem.default κ
  | _, .elim _ _ _ _, κ => KSem.default κ
  | _, .tnil, κ => KSem.default κ
  | _, .tcons _ _, κ => KSem.default κ

/-- **The realizers of a type or kind.** -/
abbrev R (ιc : Nat → Cand) (ξ : Val) (T : Tm) : Cand := interp ιc ξ T .star

variable {ιc : Nat → Cand}

/-! ## Renaming -/

/-- **Interpretation commutes with renaming.** -/
theorem interp_ren : ∀ (t : Tm) (ξ : Val) (r : Nat → Nat) (κ : SK),
    interp ιc ξ (t.ren r) κ = interp ιc (ξ ∘ r) t κ
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
  | .ind _, _, _, κ => by cases κ <;> rfl
  | .ctor _ _ _ _, _, _, _ => rfl
  | .elim _ _ _ _, _, _, _ => rfl
  | .tnil, _, _, _ => rfl
  | .tcons _ _, _, _, _ => rfl

theorem interp_shift (t : Tm) (e : Option SVal) (ξ : Val) (κ : SK) :
    interp ιc (scons e ξ) t.shift κ = interp ιc ξ t κ := by
  rw [Tm.shift, interp_ren]
  rfl

/-! ## Substitution -/

/-- The valuation a substitution induces: each variable of class `a` gets the interpretation of
its substitute at `a`. -/
def semSubst (ιc : Nat → Cand) (ξ : Val) (σ : Nat → Tm) (ρ : Nat → Option SK) : Val :=
  fun n => (ρ n).map (fun a => ⟨a, interp ιc ξ (σ n) a⟩)

theorem semSubst_shape (ξ : Val) (σ : Nat → Tm) (ρ : Nat → Option SK) :
    (semSubst ιc ξ σ ρ).shape = ρ := by
  funext n
  simp only [Val.shape, semSubst, Option.map_map]
  cases ρ n <;> rfl

/-- Lifting a substitution under a binder lifts its valuation. -/
theorem semSubst_up (e : Option SVal) (ξ : Val) (σ : Nat → Tm) (ρ : Nat → Option SK) :
    semSubst ιc (scons e ξ) (Tm.up σ) (scons (e.map SVal.κ) ρ) = scons e (semSubst ιc ξ σ ρ) := by
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
    semSubst ιc ξ (scons u Tm.var) (scons c ρ) = scons (c.map fun a => ⟨a, interp ιc ξ u a⟩) ξ := by
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
def KindOrCon (sg : Sig) (Γ : Ctx) (T : Tm) : Prop := T = .sort .box ∨ HasType sg Γ T (.sort .box)

theorem KindOrCon.sort (Γ : Ctx) (s : Srt) : KindOrCon sg Γ (.sort s) := by
  cases s with
  | star => exact .inr .sort
  | box => exact .inl rfl

/-- A kind-or-constructor that is typed is typed by `□`. -/
theorem KindOrCon.box {Γ : Ctx} {T : Tm} {s : Srt} (h : KindOrCon sg Γ T)
    (hT : HasType sg Γ T (.sort s)) : HasType sg Γ T (.sort .box) := by
  rcases h with h | h
  · subst h; exact (hT.ne_box rfl).elim
  · exact h

/-- **Interpretation commutes with a well-typed substitution.** -/
theorem HasType.interp_subst {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ)
    (hT : KindOrCon sg Γ T) {Δ : Ctx} {σ : Nat → Tm} {ξ : Val} (hΔ : Wf sg Δ)
    (hσ : SubstOk sg σ Γ Δ)
    (hk : ∀ n, (σ n).isKind = false) (hξ : ξ.shape = Δ.shape) :
    interp ιc ξ (t.subst σ) T.skel = interp ιc (semSubst ιc ξ σ Γ.shape) t T.skel := by
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
      have hpi : HasType sg Γ (.pi A B) (.sort .box) := by
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
  | ind => rfl
  | ctor =>
      exfalso
      rcases hT with h | h
      · cases h
      · exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])
  | elim _ hC =>
      exfalso
      rcases hT with h | h
      · subst h; exact hC.ne_box rfl
      · exact absurd (Conv.sort_inj (hC.unique h)) (by decide)

/-! ## Reduction -/

/-- **A well-typed reduction of a kind or constructor does not change its interpretation.** -/
theorem HasType.interp_step {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ)
    (hT : KindOrCon sg Γ T) {ξ : Val} (hξ : ξ.shape = Γ.shape) {t' : Tm} (hs : Step t t') :
    interp ιc ξ t T.skel = interp ιc ξ t' T.skel := by
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
      have hpi : HasType sg Γ (.pi A B) (.sort .box) := by
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
          have hB' : HasType sg (A₀ :: Γ) B (.sort s₂) := hB.ctx_conv hA hAA.symm
          obtain ⟨hss₂, hsk₂⟩ := hB₀.kind_conv hB' hΓ₀ hBB
          subst hss₂
          have hs₂ : s₂' = .box := (hB'.sort_box_iff hΓ₀).mpr hBk
          subst hs₂
          have hk₀ : A₀.isKind = A.isKind := by
            cases s₁' with
            | box => rw [(hA₀.sort_box_iff hΓ).mp rfl, (hA.sort_box_iff hΓ).mp rfl]
            | star => rw [hA₀.not_kind_of_sorted .sort hΓ, hA.not_kind_of_sorted .sort hΓ]
          have hsub := hb.interp_subst (ιc := ιc) hΓ₀ (.inr hB₀) hΓ (σ := scons u Tm.var) (ξ := ξ)
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
  | ind => cases hs
  | ctor =>
      exfalso
      rcases hT with h | h
      · cases h
      · exact absurd (h.isKind_of_box hΓ rfl) (by simp [Tm.isKind])
  | elim _ hC =>
      exfalso
      rcases hT with h | h
      · subst h; exact hC.ne_box rfl
      · exact absurd (Conv.sort_inj (hC.unique h)) (by decide)

theorem HasType.interp_red {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hΓ : Wf sg Γ)
    (hT : KindOrCon sg Γ T) {ξ : Val} (hξ : ξ.shape = Γ.shape) {t' : Tm} (hr : Red t t') :
    interp ιc ξ t T.skel = interp ιc ξ t' T.skel := by
  induction hr with
  | refl => rfl
  | tail hr hs ih => exact ih.trans ((h.preservation_red hΓ hr).interp_step hΓ hT hξ hs)

/-- **Convertible types have the same realizers.** -/
theorem HasType.interp_conv {Γ : Ctx} {A B : Tm} {s s' : Srt} (hA : HasType sg Γ A (.sort s))
    (hB : HasType sg Γ B (.sort s')) (hΓ : Wf sg Γ) (hc : Conv A B) {ξ : Val}
    (hξ : ξ.shape = Γ.shape) : R ιc ξ A = R ιc ξ B := by
  obtain ⟨C, hAC, hBC⟩ := hc
  have e1 := hA.interp_red (ιc := ιc) hΓ (KindOrCon.sort Γ s) hξ hAC
  have e2 := hB.interp_red (ιc := ιc) hΓ (KindOrCon.sort Γ s') hξ hBC
  simp only [Tm.skel] at e1 e2
  exact e1.trans e2.symm

/-! ## Strong normalization of lists and constructors -/

theorem sn_ind (i : Nat) : SN Step (.ind i) := .intro (fun _ h => absurd h Step.ind_inv)

theorem sn_tcons {a l : Tm} (ha : SN Step a) (hl : SN Step l) : SN Step (.tcons a l) := by
  induction ha generalizing l with
  | intro _ iha =>
      induction hl with
      | intro hl' ihl =>
          refine .intro (fun w hw => ?_)
          cases hw with
          | consH h => exact iha _ h (.intro hl')
          | consT h => exact ihl _ h

theorem sn_ctor {i k : Nat} {mask : List Bool} {as : Tm} (h : SN Step as) :
    SN Step (.ctor i k mask as) := by
  induction h with
  | intro _ ih => exact .intro (fun w hw => by cases hw with | ctorA h => exact ih _ h)

theorem sn_list : ∀ {l : Tm}, l.isList = true → (∀ j < l.toList.length, SN Step (l.nth j)) →
    SN Step l
  | .tnil, _, _ => .intro (fun _ h => absurd h Step.tnil_inv)
  | .tcons a l, hl, h =>
      sn_tcons (h 0 (by simp [Tm.toList]))
        (sn_list hl (fun j hj => h (j + 1) (by simp [Tm.toList]; omega)))
  | .var _, hl, _ => by simp [Tm.isList] at hl
  | .sort _, hl, _ => by simp [Tm.isList] at hl
  | .pi _ _, hl, _ => by simp [Tm.isList] at hl
  | .lam _ _, hl, _ => by simp [Tm.isList] at hl
  | .app _ _, hl, _ => by simp [Tm.isList] at hl
  | .ind _, hl, _ => by simp [Tm.isList] at hl
  | .ctor _ _ _ _, hl, _ => by simp [Tm.isList] at hl
  | .elim _ _ _ _, hl, _ => by simp [Tm.isList] at hl

theorem Red.ctor_inv {i k : Nat} {mask : List Bool} {as x : Tm} (h : Red (.ctor i k mask as) x) :
    ∃ as', x = .ctor i k mask as' ∧ Red as as' := by
  induction h with
  | refl => exact ⟨as, rfl, .refl⟩
  | tail _ hs ih =>
      obtain ⟨as', rfl, hr⟩ := ih
      cases hs with
      | ctorA h => exact ⟨_, rfl, hr.tail h⟩

/-- Many steps inside a list keep its length and reduce it pointwise. -/
theorem Red.list {l l' : Tm} (h : Red l l') (hl : l.isList = true) :
    l'.toList.length = l.toList.length ∧ ∀ j, Red (l.nth j) (l'.nth j) := by
  induction h with
  | refl => exact ⟨rfl, fun _ => .refl⟩
  | @tail b c hr hs ih =>
      obtain ⟨hlen, hj⟩ := ih
      have hb := Red.isList hr hl
      obtain ⟨hlen', j₀, hj₀, heq⟩ := hs.list_inv hb
      refine ⟨hlen'.trans hlen, fun j => ?_⟩
      by_cases e : j = j₀
      · subst e; exact (hj j).tail hj₀
      · rw [heq j e]; exact hj j

/-! ## The candidates of inductive types -/

/-- **Membership in an inductive type's candidate**, given candidates `ιc` for the types its
arguments may mention: strongly normalizing, and every constructor it reduces to is one of the
type's, with recursive arguments in this candidate and the others in their types' candidates.

The recursive premise is strictly positive, so this is an ordinary inductive predicate — the
least such set — and its induction principle is what proves the recursor normalizing. -/
inductive IndMem (sg : Sig) (ιc : Nat → Cand) (i : Nat) : Tm → Prop where
  | intro {t : Tm} : SN Step t →
      (∀ k mask as, Red t (.ctor i k mask as) → ∃ c, sg.ctorArgs i k = some c ∧ mask = c.mask ∧
        as.isList = true ∧ as.toList.length = c.length) →
      (∀ k mask as, Red t (.ctor i k mask as) → ∀ c j, sg.ctorArgs i k = some c →
        j < c.length → c.getD j none = none → IndMem sg ιc i (as.nth j)) →
      (∀ k mask as, Red t (.ctor i k mask as) → ∀ c j A, sg.ctorArgs i k = some c →
        c.getD j none = some A → (R ιc (fun _ => none) A).mem (as.nth j)) →
      IndMem sg ιc i t

theorem IndMem.sn {ιc : Nat → Cand} {i : Nat} {t : Tm} (h : IndMem sg ιc i t) : SN Step t := by
  cases h with | intro hsn _ _ _ => exact hsn

/-- **It is a candidate.** -/
def indCand (sg : Sig) (ιc : Nat → Cand) (i : Nat) : Cand where
  mem := IndMem sg ιc i
  sn h := h.sn
  step h hs := by
    cases h with
    | intro hsn h1 h2 h3 =>
        exact .intro (hsn.unfold hs) (fun k m as hr => h1 k m as (RTC.head hs hr))
          (fun k m as hr => h2 k m as (RTC.head hs hr))
          (fun k m as hr => h3 k m as (RTC.head hs hr))
  neutral := by
    intro t hn h
    have hred : ∀ k mask as, Red t (.ctor i k mask as) →
        ∃ t', Step t t' ∧ Red t' (.ctor i k mask as) := by
      intro k mask as hr
      rcases hr.cases_head with e | ⟨t', hs, hr'⟩
      · subst e; exact hn.elim
      · exact ⟨t', hs, hr'⟩
    refine .intro (.intro (fun t' hs => (h t' hs).sn)) (fun k m as hr => ?_)
      (fun k m as hr => ?_) (fun k m as hr => ?_)
    all_goals
      obtain ⟨t', hs, hr'⟩ := hred k m as hr
      cases h t' hs with
      | intro _ h1 h2 h3 =>
          first
            | exact h1 k m as hr'
            | exact h2 k m as hr'
            | exact h3 k m as hr'

/-- The candidates the inductive types below `i` already have. -/
def lowerC (i : Nat) (cands : (j : Nat) → j < i → Cand) : Nat → Cand :=
  fun j => if h : j < i then cands j h else snCand

/-- **The candidates of a signature's inductive types**, each built from those before it. -/
def sigCands (sg : Sig) (i : Nat) : Cand :=
  indCand sg (lowerC i (fun j _ => sigCands sg j)) i
termination_by i

/-- The candidates below `i`, as `sigCands` sees them. -/
abbrev lowerSig (sg : Sig) (i : Nat) : Nat → Cand := lowerC i (fun j _ => sigCands sg j)

theorem sigCands_eq (sg : Sig) (i : Nat) : sigCands sg i = indCand sg (lowerSig sg i) i := by
  rw [sigCands]

theorem lowerSig_lt {sg : Sig} {i j : Nat} (h : j < i) : lowerSig sg i j = sigCands sg j := by
  simp [lowerSig, lowerC, h]

/-- The realizers of an inductive type are its candidate's members. -/
theorem R_ind (ξ : Val) (i : Nat) : R (sigCands sg) ξ (.ind i) = indCand sg (lowerSig sg i) i :=
  sigCands_eq sg i

/-! ## The interpretation sees only what a term mentions -/

theorem cls_congr : ∀ {t : Tm} {n : Nat} {ρ ρ' : Nat → Option SK}, t.Scoped n →
    (∀ m < n, ρ m = ρ' m) → cls ρ t = cls ρ' t
  | .var _, _, _, _, h, hρ => hρ _ h
  | .sort _, _, _, _, _, _ => rfl
  | .pi _ _, _, _, _, _, _ => rfl
  | .lam A t, n, ρ, ρ', ⟨_, ht⟩, hρ => by
      have e : ∀ x : Option SK, ∀ m < n + 1, scons x ρ m = scons x ρ' m := fun x m hm => by
        cases m with
        | zero => rfl
        | succ m => exact hρ m (by omega)
      simp only [cls, cls_congr ht (e _)]
  | .app t u, _, _, _, ⟨ht, hu⟩, hρ => by simp only [cls, cls_congr ht hρ, cls_congr hu hρ]
  | .ind _, _, _, _, _, _ => rfl
  | .ctor _ _ _ _, _, _, _, _, _ => rfl
  | .elim _ _ _ _, _, _, _, _, _ => rfl
  | .tnil, _, _, _, _, _ => rfl
  | .tcons _ _, _, _, _, _, _ => rfl

/-- **Relevance**: the interpretation of a term depends only on the candidates of the inductive
types it mentions and the values of the variables it mentions. -/
theorem interp_congr {ιc ιc' : Nat → Cand} {i : Nat} (hι : ∀ j < i, ιc j = ιc' j) :
    ∀ (t : Tm) (n : Nat) (ξ ξ' : Val) (κ : SK), t.Scoped n → t.indsLt i →
      (∀ m < n, ξ m = ξ' m) → interp ιc ξ t κ = interp ιc' ξ' t κ
  | .var _, _, _, _, _, h, _, hξ => by simp only [interp, hξ _ h]
  | .sort _, _, _, _, _, _, _, _ => rfl
  | .pi A B, n, ξ, ξ', κ, ⟨hA, hB⟩, ⟨iA, iB⟩, hξ => by
      have e : ∀ x : Option SVal, ∀ m < n + 1, scons x ξ m = scons x ξ' m := fun x m hm => by
        cases m with
        | zero => rfl
        | succ m => exact hξ m (by omega)
      cases κ with
      | arr a b => rfl
      | star =>
          simp only [interp, interp_congr hι A n ξ ξ' _ hA iA hξ]
          split
          · congr 1
            funext x
            exact interp_congr hι B _ _ _ _ hB iB (e _)
          · congr 1
            funext _
            exact interp_congr hι B _ _ _ _ hB iB (e _)
  | .lam A t, n, ξ, ξ', κ, ⟨_, ht⟩, ⟨_, it⟩, hξ => by
      have e : ∀ x : Option SVal, ∀ m < n + 1, scons x ξ m = scons x ξ' m := fun x m hm => by
        cases m with
        | zero => rfl
        | succ m => exact hξ m (by omega)
      simp only [interp]
      split
      · cases κ with
        | star => rfl
        | arr a b =>
            funext x
            exact interp_congr hι t _ _ _ _ ht it (e _)
      · exact interp_congr hι t _ _ _ _ ht it (e _)
  | .app t u, n, ξ, ξ', κ, ⟨ht, hu⟩, ⟨it, iu⟩, hξ => by
      have hs : cls ξ.shape u = cls ξ'.shape u :=
        cls_congr hu (fun m hm => by simp only [Val.shape, hξ m hm])
      simp only [interp, hs]
      cases cls ξ'.shape u with
      | none => exact interp_congr hι t _ _ _ _ ht it hξ
      | some a =>
          dsimp only
          rw [interp_congr hι t _ _ _ _ ht it hξ, interp_congr hι u _ _ _ _ hu iu hξ]
  | .ind j, _, _, _, κ, _, hj, _ => by
      cases κ with
      | star => exact hι j hj
      | arr a b => rfl
  | .ctor _ _ _ _, _, _, _, _, _, _, _ => rfl
  | .elim _ _ _ _, _, _, _, _, _, _, _ => rfl
  | .tnil, _, _, _, _, _, _, _ => rfl
  | .tcons _ _, _, _, _, _, _, _, _ => rfl

/-- **An argument type's realizers are what the inductive's own candidate assumed them to be.** -/
theorem R_arg_eq (hsg : WfSig sg) {i k : Nat} {c : CtorSpec} (hc : sg.ctorArgs i k = some c)
    {A : Tm} (hA : some A ∈ c) (ξ : Val) :
    R (sigCands sg) ξ A = R (lowerSig sg i) (fun _ => none) A :=
  interp_congr (fun _ hj => (lowerSig_lt hj).symm) A 0 ξ _ _ (sg.ctorArgs_closed hc _ hA)
    (hsg i k c hc A hA).2 (fun _ hm => absurd hm (Nat.not_lt_zero _))

/-! ## Spines through arrow types -/

/-- Terms realizing a list of types, pointwise. -/
inductive MemList (ιc : Nat → Cand) (ξ : Val) : List Tm → List Tm → Prop where
  | nil : MemList ιc ξ [] []
  | cons {a d : Tm} {as ds : List Tm} : (R ιc ξ d).mem a → MemList ιc ξ as ds →
      MemList ιc ξ (a :: as) (d :: ds)

theorem MemList.append {ξ : Val} {as ds bs es : List Tm} (h₁ : MemList ιc ξ as ds)
    (h₂ : MemList ιc ξ bs es) : MemList ιc ξ (as ++ bs) (ds ++ es) := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => exact .cons ha ih

theorem MemList.of_getD {ξ : Val} : ∀ {as ds : List Tm} (d₀ : Tm), as.length = ds.length →
    (∀ j < ds.length, (R ιc ξ (ds.getD j d₀)).mem (as.getD j d₀)) → MemList ιc ξ as ds
  | [], [], _, _, _ => .nil
  | a :: as, d :: ds, d₀, hl, h =>
      .cons (h 0 (by simp)) (MemList.of_getD d₀ (by simpa using hl) (fun j hj => by
        simpa using h (j + 1) (by simp; omega)))
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- **Applying a realizer of an arrow type to realizers of its domains** realizes the codomain. -/
theorem R_arrows_apps {ξ : Val} {c : Tm} :
    ∀ {ds as : List Tm} {f : Tm}, (∀ d ∈ ds, d.isKind = false) →
      (R ιc ξ (arrows ds c)).mem f → MemList ιc ξ as ds → (R ιc ξ c).mem (Tm.apps f as)
  | [], [], _, _, hf, _ => hf
  | d :: ds, a :: as, f, hk, hf, .cons ha hrest => by
      have hd : d.isKind = false := hk d (by simp)
      change (interp ιc ξ (.pi d (arrows ds c).shift) .star).mem f at hf
      simp only [interp, hd, Bool.false_eq_true, if_false] at hf
      have h1 := hf a ha ()
      rw [interp_shift] at h1
      exact R_arrows_apps (ds := ds) (as := as) (f := .app f a) (fun e he => hk e (by simp [he]))
        h1 hrest

/-! ## Constructors and the recursor are reducible -/

/-- **A constructor applied to realizers of its argument types is in the inductive's
candidate.** -/
theorem IndMem.ctor (hsg : WfSig sg) {i k : Nat} {c : CtorSpec} (hc : sg.ctorArgs i k = some c)
    {as : Tm} (hl : as.isList = true) (hlen : as.toList.length = c.length) {ξ : Val}
    (ha : ∀ j < c.length, (R (sigCands sg) ξ (argTy i (c.getD j none))).mem (as.nth j)) :
    IndMem sg (lowerSig sg i) i (.ctor i k c.mask as) := by
  have hsn : ∀ j < as.toList.length, SN Step (as.nth j) :=
    fun j hj => Cand.sn _ (ha j (hlen ▸ hj))
  refine .intro (sn_ctor (sn_list hl hsn)) (fun k' m as' hr => ?_) (fun k' m as' hr => ?_)
    (fun k' m as' hr => ?_)
  · obtain ⟨as'', e, hr'⟩ := Red.ctor_inv hr
    cases e
    obtain ⟨hlen', _⟩ := hr'.list hl
    exact ⟨c, hc, rfl, hr'.isList hl, hlen'.trans hlen⟩
  · intro c' j hc' hj hnone
    obtain ⟨as'', e, hr'⟩ := Red.ctor_inv hr
    cases e
    rw [hc] at hc'
    cases hc'
    have := ha j hj
    rw [hnone] at this
    simp only [argTy] at this
    rw [R_ind] at this
    exact (indCand sg _ i).red this ((hr'.list hl).2 j)
  · intro c' j A hc' hA
    obtain ⟨as'', e, hr'⟩ := Red.ctor_inv hr
    cases e
    rw [hc] at hc'
    cases hc'
    have hj : j < c.length := by
      rcases Nat.lt_or_ge j c.length with h | h
      · exact h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hA
        cases hA
    have := ha j hj
    rw [hA] at this
    simp only [argTy] at this
    have hmem : some A ∈ c := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at hA
      simp only [Option.getD_some] at hA
      exact hA ▸ List.getElem_mem hj
    rw [R_arg_eq hsg hc hmem] at this
    exact Cand.red _ this ((hr'.list hl).2 j)

theorem MemList.recCalls {ξ : Val} {X : Cand} {i : Nat} {C C' bs : Tm} (hX : R ιc ξ C = X) :
    ∀ (as : List Tm) (c : CtorSpec), as.length = c.length →
      (∀ j < c.length, c.getD j none = none → X.mem (.elim i C' bs (as.getD j (.sort .star)))) →
      MemList ιc ξ (Tm.recCalls i C' bs as c.mask) (List.replicate c.recCount C)
  | [], [], _, _ => .nil
  | a :: as, o :: c, hl, h => by
      have ih := MemList.recCalls hX as c (by simpa using hl) (fun j hj hn => by
        simpa using h (j + 1) (by simp; omega) (by simpa using hn))
      cases o with
      | none =>
          have ha := h 0 (by simp) rfl
          simp only [List.getD_cons_zero] at ha
          simpa [Tm.recCalls, CtorSpec.mask, CtorSpec.recCount, List.replicate_succ] using
            MemList.cons (hX ▸ ha) ih
      | some A =>
          simpa [Tm.recCalls, CtorSpec.mask, CtorSpec.recCount] using ih
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **The recursor is reducible**: applied to a member of the inductive's candidate, normalizing
branches realizing their types, and a normalizing motive, it realizes the motive. By induction on
the membership — which gives the recursive calls — and then on the normalization of the parts. -/
theorem elim_mem (hsg : WfSig sg) {ξ : Val} {i : Nat} {C : Tm} (hCk : C.isKind = false)
    (hargk : ∀ k c, sg.ctorArgs i k = some c → ∀ o ∈ c, (argTy i o).isKind = false) :
    ∀ {t : Tm}, IndMem sg (lowerSig sg i) i t → ∀ {C' bs : Tm}, SN Step C' → SN Step bs →
      bs.isList = true →
      (∀ k c, sg.ctorArgs i k = some c → (R (sigCands sg) ξ (branchTy i c C)).mem (bs.nth k)) →
      (R (sigCands sg) ξ C).mem (.elim i C' bs t) := by
  intro t ht
  induction ht with
  | @intro t hsn hshape hrec hnon ih =>
      intro C' bs hC' hbs hbl hbr
      have key : ∀ t₁, Red t t₁ → SN Step t₁ → ∀ C' bs, SN Step C' → SN Step bs →
          bs.isList = true →
          (∀ k c, sg.ctorArgs i k = some c → (R (sigCands sg) ξ (branchTy i c C)).mem (bs.nth k)) →
          (R (sigCands sg) ξ C).mem (.elim i C' bs t₁) := by
        intro t₁ hr hsn₁
        induction hsn₁ with
        | @intro t₁ hsn₁ iht₁ =>
            intro C' bs hC'
            induction hC' generalizing bs with
            | @intro C' hC'' ihC =>
                intro hbs
                induction hbs with
                | @intro bs hbs' ihbs =>
                    intro hbl hbr
                    refine Cand.neutral _ trivial (fun w hw => ?_)
                    cases hw with
                    | elimC h => exact ihC _ h bs (.intro hbs') hbl hbr
                    | elimB h =>
                        obtain ⟨_, j₀, hj₀, heq⟩ := h.list_inv hbl
                        refine ihbs _ h (h.isList hbl) (fun k c hc => ?_)
                        by_cases e : k = j₀
                        · subst e; exact Cand.step _ (hbr k c hc) hj₀
                        · rw [heq k e]; exact hbr k c hc
                    | elimT h =>
                        exact iht₁ _ h (hr.tail h) C' bs (.intro hC'') (.intro hbs') hbl hbr
                    | @iota _ k mask _ _ as _ hal =>
                        obtain ⟨c, hc, hmask, _, hlen⟩ := hshape k mask as hr
                        subst hmask
                        have hb := hbr k c hc
                        refine R_arrows_apps (fun d hd => ?_) hb (MemList.append ?_ ?_)
                        · rcases List.mem_append.mp hd with hd | hd
                          · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
                            exact hargk k c hc o ho
                          · rw [List.eq_of_mem_replicate hd]; exact hCk
                        · refine MemList.of_getD (.sort .star) (by simpa using hlen)
                            (fun j hj => ?_)
                          have hj' : j < c.length := by simpa using hj
                          have e1 : (c.map (argTy i)).getD j (.sort .star) =
                              argTy i (c.getD j none) := by
                            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
                          have e2 : as.toList.getD j (.sort .star) = as.nth j := rfl
                          rw [e1, e2]
                          cases hcj : c.getD j none with
                          | none =>
                              simp only [argTy]
                              rw [R_ind]
                              exact hrec k c.mask as hr c j hc hj' hcj
                          | some A =>
                              have hmem : some A ∈ c := by
                                rw [List.getD_eq_getElem?_getD,
                                  List.getElem?_eq_getElem hj'] at hcj
                                simp only [Option.getD_some] at hcj
                                exact hcj ▸ List.getElem_mem hj'
                              simp only [argTy]
                              rw [R_arg_eq hsg hc hmem]
                              exact hnon k c.mask as hr c j A hc hcj
                        · exact MemList.recCalls rfl as.toList c hlen (fun j hj hn =>
                            ih k c.mask as hr c j hc hj hn (.intro hC'') (.intro hbs') hbl hbr)
      exact key t .refl hsn C' bs hC' hbs hbl hbr

/-! ## The fundamental theorem -/

/-- **Every well-typed term realizes its type**, under any substitution of realizers. -/
theorem HasType.fundamental (hsg : WfSig sg) {Γ : Ctx} {M T : Tm} (h : HasType sg Γ M T)
    (hΓ : Wf sg Γ) {ξ : Val}
    {σ : Nat → Tm} (hξ : ξ.shape = Γ.shape)
    (hσ : ∀ n A, Γ.lookup n = some A → (R (sigCands sg) ξ A).mem (σ n)) :
    (R (sigCands sg) ξ T).mem (M.subst σ) := by
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
                show (interp (sigCands sg) (scons e ξ) A.shift .star).mem _
                rw [interp_shift]
                exact Cand.var _ 0
            | succ n =>
                simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hC
                obtain ⟨C', hC', rfl⟩ := hC
                show (interp (sigCands sg) (scons e ξ) C'.shift .star).mem _
                rw [interp_shift]
                exact hσ n C' hC')
      rw [← Tm.up_inst] at hsB
      exact sn_pi hsA (sn_of_subst hsB)
  | @lam Γ A t B s₁ s₂ hA ht hB ihA iht _ =>
      have hsA : SN Step (A.subst σ) := ihA hΓ hξ hσ
      have key : ∀ (e : Option SVal), e.map SVal.κ = A.cls₀ → ∀ N, (R (sigCands sg) ξ A).mem N →
          (R (sigCands sg) (scons e ξ) B).mem (.app ((Tm.lam A t).subst σ) N) := by
        intro e he N hN
        refine Cand.beta _ hsA ((R (sigCands sg) ξ A).sn hN) ?_
        rw [Tm.up_inst]
        exact iht (hΓ.cons hA) (ξ := scons e ξ)
          (by rw [Val.shape_scons, hξ, Ctx.shape_cons, he])
          (fun n C hC => by
            cases n with
            | zero =>
                simp only [Ctx.lookup_zero, Option.some.injEq] at hC
                subst hC
                show (interp (sigCands sg) (scons e ξ) A.shift .star).mem _
                rw [interp_shift]
                exact hN
            | succ n =>
                simp only [Ctx.lookup_succ, Option.map_eq_some_iff] at hC
                obtain ⟨C', hC', rfl⟩ := hC
                show (interp (sigCands sg) (scons e ξ) C'.shift .star).mem _
                rw [interp_shift]
                exact hσ n C' hC')
      show (interp (sigCands sg) ξ (.pi A B) .star).mem _
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
      have hsub := hB.interp_subst (ιc := sigCands sg) (hΓ.cons hA) (KindOrCon.sort _ s₂) hΓ
        (σ := scons u Tm.var)
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
      show (interp (sigCands sg) ξ (B.inst u) .star).mem (.app (t.subst σ) (u.subst σ))
      rw [show B.inst u = B.subst (scons u Tm.var) from rfl, hsub]
      change (interp (sigCands sg) ξ (.pi A B) .star).mem (t.subst σ) at hft
      simp only [interp] at hft
      cases hAk : A.isKind with
      | false =>
          simp only [hAk, Bool.false_eq_true, if_false] at hft
          simpa [Tm.cls₀, hAk] using hft _ hfu ()
      | true =>
          simp only [hAk, if_true] at hft
          simpa [Tm.cls₀, hAk] using hft _ hfu (interp (sigCands sg) ξ u A.skel)
  | @conv Γ t A B s ht hB hc iht _ =>
      have hA : A ≠ .sort .box := fun e => by subst e; exact hB.conv_box_eq hΓ hc
      obtain ⟨s', hs'⟩ := (ht.correct hΓ).resolve_left hA
      rw [← hs'.interp_conv hB hΓ hc hξ]
      exact iht hΓ hξ hσ
  | ind => exact sn_ind _
  | @ctor Γ i k mask as c hc hm hl hlen _ iha =>
      subst hm
      show (R (sigCands sg) ξ (.ind i)).mem (.ctor i k c.mask (as.subst σ))
      rw [R_ind]
      refine IndMem.ctor hsg hc (Tm.isList_subst _ _ hl)
        (by rw [Tm.toList_subst _ _ hl, List.length_map, hlen]) (ξ := ξ) (fun j hj => ?_)
      rw [Tm.nth_subst hl]
      exact iha j hj hΓ hξ hσ
  | @elim Γ i m C bs t hm hC hl hlen _ harg _ ihC ihb _ iht =>
      have hCs : SN Step (C.subst σ) := ihC hΓ hξ hσ
      have hts := iht hΓ hξ hσ
      rw [R_ind] at hts
      have hbr : ∀ k c, sg.ctorArgs i k = some c →
          (R (sigCands sg) ξ (branchTy i c C)).mem ((bs.subst σ).nth k) := fun k c hc => by
        rw [Tm.nth_subst hl]; exact ihb k c hc hΓ hξ hσ
      have hbsn : SN Step (bs.subst σ) := sn_list (Tm.isList_subst _ _ hl) (fun j hj => by
        rw [Tm.toList_subst _ _ hl, List.length_map, hlen] at hj
        obtain ⟨c, hc⟩ := Sig.ctorArgs_of_lt hm hj
        exact Cand.sn _ (hbr j c hc))
      exact elim_mem hsg (hC.not_kind_of_sorted .sort hΓ)
        (fun k c hc o ho => (harg k c hc o ho).not_kind_of_sorted .sort hΓ) hts hCs hbsn
        (Tm.isList_subst _ _ hl) hbr

/-! ## Strong normalization -/

/-- **Strong normalization**: every well-typed term in a valid context is strongly
normalizing. -/
theorem HasType.sn {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hsg : WfSig sg)
    (hΓ : Wf sg Γ) : SN Step t := by
  let ξ : Val := fun n => (Γ.shape n).map fun a => ⟨a, default⟩
  have hξ : ξ.shape = Γ.shape := by
    funext n
    simp only [Val.shape, ξ, Option.map_map]
    cases Γ.shape n <;> rfl
  have := h.fundamental hsg hΓ hξ (σ := Tm.var) (fun n _ _ => Cand.var _ n)
  rw [Tm.subst_var] at this
  exact (R (sigCands sg) ξ T).sn this

/-- Every type is strongly normalizing too — `□` trivially, anything else by being typed. -/
theorem HasType.sn_type {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) (hsg : WfSig sg)
    (hΓ : Wf sg Γ) : SN Step T := by
  rcases h.correct hΓ with e | ⟨s, hs⟩
  · subst e; exact sn_sort _
  · exact hs.sn hsg hΓ

end LambdaLab.Languages.CoIC.DeBruijn
