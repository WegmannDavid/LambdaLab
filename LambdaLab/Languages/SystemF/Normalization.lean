import LambdaLab.Languages.SystemF.Reduction

/-!
# System F — strong normalization, by reducibility candidates

Every well-typed term is strongly normalizing under full β (`HasType.sn`). This is Girard's
argument; what follows is it, in the order it has to be built.

## Candidates

A **reducibility candidate** is a set of terms that

* (CR1) contains only strongly normalizing terms,
* (CR2) is closed under reduction, and
* (CR3) contains every neutral term all of whose reducts it contains.

The strongly normalizing terms themselves form one (`snCand`), and by CR3 every candidate contains
every variable (`Cand.var`) — a variable is neutral and has no reducts.

## Interpreting types

A type is interpreted relative to an assignment `ρ` of a candidate to each type variable:

    ⟦n⟧ρ      = ρ n
    ⟦A → B⟧ρ  = { t | ∀ u ∈ ⟦A⟧ρ, t u ∈ ⟦B⟧ρ }
    ⟦∀ A⟧ρ    = { t | ∀ B, ∀ candidate C, t [B] ∈ ⟦A⟧(C . ρ) }

The quantification over *all* candidates in the last line is the impredicativity that makes System
F hard; in Lean it is an ordinary `∀` inside a `Prop`, which `Prop`'s own impredicativity allows.
Note that the type `B` a term is instantiated at and the candidate `C` its variable is interpreted
by are independent — which is what lets the fundamental lemma below keep a type substitution `σ`
and a candidate assignment `ρ` side by side, unrelated.

Every interpretation is a candidate (`red_cr`), by induction on the type. Interpretation commutes
with renaming and substitution of the type (`red_ren`, `red_subst`), so instantiating a `∀` is
interpreting with the argument's candidate (`red_inst`).

## The fundamental lemma

If `Δ; Γ ⊢ t : A`, then for any type substitution `σ`, candidate assignment `ρ`, and term
substitution `γ` sending each variable of `Γ` into the interpretation of its type,
`(t.tsubst σ).subst γ ∈ ⟦A⟧ρ` (`fundamental`). The abstraction cases are the only real work
(`red_lam`, `red_tlam`): a β-redex is neutral, so CR3 applies, by induction on the normalization
of its parts.

Instantiating everything with identities — `σ = var`, `γ = var`, and every type variable
interpreted by `snCand` — puts `t` itself in a candidate, and CR1 finishes.
-/

namespace LambdaLab.Languages.SystemF

/-! ## Candidates -/

/-- **A reducibility candidate.** -/
structure Cand where
  /-- The terms it contains. -/
  mem : Tm → Prop
  /-- CR1: they normalize. -/
  sn : ∀ {t}, mem t → SN Step t
  /-- CR2: it is closed under reduction. -/
  step : ∀ {t t'}, mem t → Step t t' → mem t'
  /-- CR3: a neutral term whose reducts it contains, it contains. -/
  neutral : ∀ {t}, t.Neutral → (∀ t', Step t t' → mem t') → mem t

/-- The strongly normalizing terms are a candidate. -/
def snCand : Cand where
  mem t := SN Step t
  sn h := h
  step h s := h.unfold s
  neutral _ h := .intro h

/-- Every candidate contains every variable. -/
theorem Cand.var (C : Cand) (n : Nat) : C.mem (.var n) :=
  C.neutral trivial (fun _ s => absurd s Step.var_inv)

/-! ## Interpretation -/

/-- **The interpretation of a type**, given a candidate for each type variable. -/
def Red : Ty → (Nat → Cand) → Tm → Prop
  | .var n, ρ, t => (ρ n).mem t
  | .arr A B, ρ, t => ∀ u, Red A ρ u → Red B ρ (.app t u)
  | .all A, ρ, t => ∀ (B : Ty) (C : Cand), Red A (scons C ρ) (.tapp t B)

/-- **Every interpretation is a candidate**: CR1, CR2 and CR3, together, by induction on the
type. -/
theorem red_cr : ∀ (A : Ty) (ρ : Nat → Cand),
    (∀ {t}, Red A ρ t → SN Step t) ∧
    (∀ {t t'}, Red A ρ t → Step t t' → Red A ρ t') ∧
    (∀ {t}, t.Neutral → (∀ t', Step t t' → Red A ρ t') → Red A ρ t)
  | .var n, ρ => ⟨(ρ n).sn, (ρ n).step, (ρ n).neutral⟩
  | .arr A B, ρ => by
      obtain ⟨a1, a2, a3⟩ := red_cr A ρ
      obtain ⟨b1, b2, b3⟩ := red_cr B ρ
      refine ⟨?_, ?_, ?_⟩
      · -- CR1: apply to a variable, which every candidate contains
        intro t ht
        have hx : Red A ρ (.var 0) := a3 trivial (fun _ s => absurd s Step.var_inv)
        exact sn_app_left (b1 (ht _ hx))
      · intro t t' ht hs u hu
        exact b2 (ht u hu) (.appL hs)
      · -- CR3: an application of a neutral head, by induction on the argument's normalization
        intro t hn hred u hu
        have key : ∀ u, SN Step u → Red A ρ u → Red B ρ (.app t u) := by
          intro u hsn
          induction hsn with
          | @intro u _ ih =>
              intro hu
              refine b3 trivial ?_
              intro w hw
              rcases Step.app_neutral hn hw with ⟨t', ht', rfl⟩ | ⟨u', hu', rfl⟩
              · exact hred t' ht' u hu
              · exact ih u' hu' (a2 hu hu')
        exact key u (a1 hu) hu
  | .all A, ρ => by
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        exact sn_tapp_left ((red_cr A (scons snCand ρ)).1 (ht (.var 0) snCand))
      · intro t t' ht hs B C
        exact (red_cr A (scons C ρ)).2.1 (ht B C) (.tappL hs)
      · intro t hn hred B C
        refine (red_cr A (scons C ρ)).2.2 trivial ?_
        intro w hw
        obtain ⟨t', ht', rfl⟩ := Step.tapp_neutral hn hw
        exact hred t' ht' B C

/-- The interpretation of a type, as a candidate. -/
def RedC (A : Ty) (ρ : Nat → Cand) : Cand where
  mem := Red A ρ
  sn := (red_cr A ρ).1
  step := (red_cr A ρ).2.1
  neutral := (red_cr A ρ).2.2

/-- Interpretation depends only on what the assigned candidates contain. -/
theorem red_congr : ∀ (A : Ty) {ρ ρ' : Nat → Cand}, (∀ n t, (ρ n).mem t ↔ (ρ' n).mem t) →
    ∀ t, Red A ρ t ↔ Red A ρ' t
  | .var n, _, _, h, t => h n t
  | .arr A B, _, _, h, t => by
      constructor
      · intro ht u hu
        exact (red_congr B h _).mp (ht u ((red_congr A h u).mpr hu))
      · intro ht u hu
        exact (red_congr B h _).mpr (ht u ((red_congr A h u).mp hu))
  | .all A, ρ, ρ', h, t => by
      have h' : ∀ (C : Cand) n w, (scons C ρ n).mem w ↔ (scons C ρ' n).mem w := by
        intro C n w
        cases n with
        | zero => exact Iff.rfl
        | succ n => exact h n w
      constructor
      · intro ht B C
        exact (red_congr A (h' C) _).mp (ht B C)
      · intro ht B C
        exact (red_congr A (h' C) _).mpr (ht B C)

theorem scons_upRen {X : Type} (x : X) (ρ : Nat → X) (ξ : Nat → Nat) :
    (fun n => scons x ρ (upRen ξ n)) = scons x (fun n => ρ (ξ n)) := by
  funext n; cases n <;> rfl

/-- **Interpretation commutes with renaming the type.** -/
theorem red_ren : ∀ (A : Ty) (ξ : Nat → Nat) (ρ : Nat → Cand) (t : Tm),
    Red (A.ren ξ) ρ t ↔ Red A (fun n => ρ (ξ n)) t
  | .var _, _, _, _ => Iff.rfl
  | .arr A B, ξ, ρ, t => by
      constructor
      · intro ht u hu
        exact (red_ren B ξ ρ _).mp (ht u ((red_ren A ξ ρ u).mpr hu))
      · intro ht u hu
        exact (red_ren B ξ ρ _).mpr (ht u ((red_ren A ξ ρ u).mp hu))
  | .all A, ξ, ρ, t => by
      constructor
      · intro ht B C
        have := (red_ren A (upRen ξ) (scons C ρ) _).mp (ht B C)
        rwa [scons_upRen] at this
      · intro ht B C
        refine (red_ren A (upRen ξ) (scons C ρ) _).mpr ?_
        rw [scons_upRen]
        exact ht B C

/-- **Interpretation commutes with substituting into the type**: the substituted type means what
the original does with each variable interpreted by its replacement. -/
theorem red_subst : ∀ (A : Ty) (σ : Nat → Ty) (ρ : Nat → Cand) (t : Tm),
    Red (A.subst σ) ρ t ↔ Red A (fun n => RedC (σ n) ρ) t
  | .var _, _, _, _ => Iff.rfl
  | .arr A B, σ, ρ, t => by
      constructor
      · intro ht u hu
        exact (red_subst B σ ρ _).mp (ht u ((red_subst A σ ρ u).mpr hu))
      · intro ht u hu
        exact (red_subst B σ ρ _).mpr (ht u ((red_subst A σ ρ u).mp hu))
  | .all A, σ, ρ, t => by
      have hpt : ∀ (C : Cand) n w,
          (RedC (Ty.up σ n) (scons C ρ)).mem w ↔ (scons C (fun m => RedC (σ m) ρ) n).mem w := by
        intro C n w
        cases n with
        | zero => exact Iff.rfl
        | succ n => exact red_ren (σ n) Nat.succ (scons C ρ) w
      constructor
      · intro ht B C
        exact (red_congr A (hpt C) _).mp ((red_subst A (Ty.up σ) (scons C ρ) _).mp (ht B C))
      · intro ht B C
        exact (red_subst A (Ty.up σ) (scons C ρ) _).mpr ((red_congr A (hpt C) _).mpr (ht B C))

/-- **Instantiating a `∀` is interpreting its variable by the argument's interpretation.** -/
theorem red_inst (A B : Ty) (ρ : Nat → Cand) (t : Tm) :
    Red (A.inst B) ρ t ↔ Red A (scons (RedC B ρ) ρ) t :=
  (red_subst A (scons B Ty.var) ρ t).trans
    (red_congr A (fun n _ => by cases n <;> exact Iff.rfl) t)

/-! ## Abstractions -/

theorem red_lam_aux {A B : Ty} {ρ : Nat → Cand} {A' : Ty} {body : Tm} (hb : SN Step body) :
    (∀ u, Red A ρ u → Red B ρ (body.inst u)) →
      ∀ u, SN Step u → Red A ρ u → Red B ρ (.app (.lam A' body) u) := by
  induction hb with
  | @intro body _ ihb =>
      intro h u hu
      induction hu with
      | @intro u hallu ihu =>
          intro hred
          refine (RedC B ρ).neutral trivial ?_
          intro w hw
          cases hw with
          | beta => exact h u hred
          | appL hs =>
              obtain ⟨body', hb', rfl⟩ := Step.lam_inv hs
              exact ihb body' hb' (fun u' hu' => (RedC B ρ).step (h u' hu') (hb'.subst _)) u
                (.intro hallu) hred
          | appR hs => exact ihu _ hs ((RedC A ρ).step hred hs)

/-- **An abstraction is reducible** when every instance of its body at a reducible argument is. -/
theorem red_lam {A B : Ty} {ρ : Nat → Cand} {A' : Ty} {body : Tm}
    (h : ∀ u, Red A ρ u → Red B ρ (body.inst u)) : Red (.arr A B) ρ (.lam A' body) := by
  have hb : SN Step body := sn_of_subst ((RedC B ρ).sn (h _ ((RedC A ρ).var 0)))
  intro u hu
  exact red_lam_aux hb h u ((RedC A ρ).sn hu) hu

theorem red_tlam_aux {A : Ty} {ρ : Nat → Cand} {body : Tm} (hb : SN Step body) :
    (∀ B C, Red A (scons C ρ) (body.tinst B)) →
      ∀ B C, Red A (scons C ρ) (.tapp (.tlam body) B) := by
  induction hb with
  | @intro body _ ihb =>
      intro h B C
      refine (RedC A (scons C ρ)).neutral trivial ?_
      intro w hw
      cases hw with
      | tbeta => exact h B C
      | tappL hs =>
          obtain ⟨body', hb', rfl⟩ := Step.tlam_inv hs
          exact ihb body' hb' (fun B' C' => (RedC A (scons C' ρ)).step (h B' C') (hb'.tsubst _)) B C

/-- **A type abstraction is reducible** when every instance of its body is, at any type and any
candidate. -/
theorem red_tlam {A : Ty} {ρ : Nat → Cand} {body : Tm}
    (h : ∀ B C, Red A (scons C ρ) (body.tinst B)) : Red (.all A) ρ (.tlam body) :=
  red_tlam_aux (sn_of_tsubst ((RedC A (scons snCand ρ)).sn (h (.var 0) snCand))) h

/-! ## The fundamental lemma -/

theorem inst_up_eq (t u : Tm) (γ : Nat → Tm) :
    (t.subst (Tm.up γ)).inst u = t.subst (scons u γ) := by
  simp only [Tm.inst, Tm.subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [Tm.up_succ, Tm.subst_ren]
      exact Tm.subst_var _

theorem tinst_up_eq (t : Tm) (B : Ty) (σ : Nat → Ty) (γ : Nat → Tm) :
    ((t.tsubst (Ty.up σ)).subst (Tm.tup γ)).tinst B = (t.tsubst (scons B σ)).subst γ := by
  rw [← Tm.tinst_subst]
  congr 1
  simp only [Tm.tinst, Tm.tsubst_tsubst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [Ty.up_succ, Ty.subst_ren]
      exact Ty.subst_var _

/-- **The fundamental lemma**: a well-typed term, under any type substitution, any candidate
assignment, and any substitution of reducible terms for its variables, is reducible. -/
theorem fundamental {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    ∀ (σ : Nat → Ty) (ρ : Nat → Cand) (γ : Nat → Tm),
      (∀ n B, Γ[n]? = some B → Red B ρ (γ n)) → Red A ρ ((t.tsubst σ).subst γ) := by
  induction h with
  | var hn => intro _ _ _ hγ; exact hγ _ _ hn
  | @lam Δ Γ A t B _ _ ih =>
      intro σ ρ γ hγ
      show Red (.arr A B) ρ (.lam (A.subst σ) ((t.tsubst σ).subst (Tm.up γ)))
      refine red_lam ?_
      intro u hu
      rw [inst_up_eq]
      refine ih σ ρ (scons u γ) ?_
      intro n C hn
      cases n with
      | zero => cases hn; exact hu
      | succ n => exact hγ n C hn
  | app _ _ ih₁ ih₂ =>
      intro σ ρ γ hγ
      exact ih₁ σ ρ γ hγ _ (ih₂ σ ρ γ hγ)
  | @tlam Δ Γ t A _ ih =>
      intro σ ρ γ hγ
      show Red (.all A) ρ (.tlam ((t.tsubst (Ty.up σ)).subst (Tm.tup γ)))
      refine red_tlam ?_
      intro B C
      rw [tinst_up_eq]
      refine ih (scons B σ) (scons C ρ) γ ?_
      intro n B' hn
      obtain ⟨B₀, hB₀, rfl⟩ := HasType.getElem?_map_eq_some hn
      exact (red_ren B₀ Nat.succ (scons C ρ) (γ n)).mpr (hγ n B₀ hB₀)
  | @tapp Δ Γ t A B _ _ ih =>
      intro σ ρ γ hγ
      show Red (A.inst B) ρ (.tapp ((t.tsubst σ).subst γ) (B.subst σ))
      exact (red_inst A B ρ _).mpr (ih σ ρ γ hγ (B.subst σ) (RedC B ρ))

/-- **Strong normalization**: every well-typed term is strongly normalizing. -/
theorem HasType.sn {Δ : Nat} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Δ Γ t A) :
    SN Step t := by
  have := fundamental h Ty.var (fun _ => snCand) Tm.var (fun n B _ => (RedC B _).var n)
  rw [Tm.tsubst_var, Tm.subst_var] at this
  exact (RedC A _).sn this

end LambdaLab.Languages.SystemF
