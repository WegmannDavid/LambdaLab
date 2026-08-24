import LambdaLab.Nominal.Unification.Basic
import LambdaLab.Nominal.Unification.Soundness
import LambdaLab.Nominal.Unification.Completeness

open LambdaLab.Nominal

/-! # Most-generality of `unifyList`

When `unifyList` succeeds, the returned unifier is at least as general as any other unifier of
the same equation set — where "unifier" means *any* substitution making the equations hold, as in
the standard definition, not merely one in the algorithm's own list format.

Generality is measured by `MoreGeneral` on `Subst A α` (`Substitution/Basic.lean`). A list-form
counterpart was dropped: the algorithm's output converts to a `Subst` via `toSubst`, and the
hypothetical unifier is a `Subst` to begin with, so nothing needs the list-level notion. -/

/-- **Most-generality of `unifyList`.** When `unifyList eqs = some u`, `u` is at
least as general as any other unifier of `eqs`. Proved by induction on
`unifyList.induct`, using `Signature.unifier_absorb` in the var-elim cases
and `Signature.decomp_unifier_sound` in the decompose case. -/
theorem unifyList_mgu {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (u : Unifier A α),
      unifyList eqs = some u →
      ∀ (σ : Subst A α), Subst.Unifies σ eqs →
      MoreGeneral u.toSubst σ := by
  intro eqs
  induction eqs using unifyList.induct with
  | case1 =>
      intro u hu σ _
      have hueq : ([] : Unifier A α) = u := by grind [unifyList]
      subst hueq
      exact ⟨σ, fun t => by simp [Unifier.toSubst_nil, Signature.hasSubst_pSubst_eq,
        Signature.pSubst_empty]⟩
  | case2 x y eqs' m hxv hyv ih =>
      intro u hu σ hσ
      have hu : unifyList eqs' = some u := by grind [unifyList]
      exact ih u hu σ (fun p hp => hσ p (List.mem_cons_of_mem _ hp))
  | case3 _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case4 x y eqs' m hxv hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hueq : (m, y) :: rest = u := by grind [unifyList]
      subst hueq
      have hxeq : x = Signature.var m := Signature.var_of_isVar x m hxv
      have hxy : Signature.pSubst (Signature.var m) σ = Signature.pSubst y σ := hxeq ▸ Subst.Unifies.head_eq hσ
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m y) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m y hxy,
            Signature.unifier_absorb σ q.2 m y hxy]
        exact hq_unif
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : HasSubst.pSubst (HasSubst.single t m y) σ = HasSubst.pSubst t σ :=
        Signature.unifier_absorb σ t m y hxy
      have hrec := hτ (HasSubst.single t m y)
      rw [Unifier.toSubst_cons_pSubst, ← habs]
      exact hrec
  | case5 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case6 _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case7 x y eqs' hxv m hyv hocc rest hrest ih =>
      intro u hu σ hσ
      have hueq : (m, x) :: rest = u := by grind [unifyList]
      subst hueq
      have hyeq : y = Signature.var m := Signature.var_of_isVar y m hyv
      have hxy : Signature.pSubst (Signature.var m) σ = Signature.pSubst x σ := (hyeq ▸ Subst.Unifies.head_eq hσ).symm
      have hσ_sub : Subst.Unifies σ (HasSubst.single eqs' m x) := by
        intro p hp
        rw [Equations.single_eq] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, hqeq⟩
        subst hqeq
        have hq_unif := hσ q (List.mem_cons_of_mem _ hq)
        simp only [Signature.hasSubst_pSubst_eq]
        rw [Signature.unifier_absorb σ q.1 m x hxy,
            Signature.unifier_absorb σ q.2 m x hxy]
        exact hq_unif
      obtain ⟨τ, hτ⟩ := ih rest hrest σ hσ_sub
      refine ⟨τ, fun t => ?_⟩
      have habs : HasSubst.pSubst (HasSubst.single t m x) σ = HasSubst.pSubst t σ :=
        Signature.unifier_absorb σ t m x hxy
      have hrec := hτ (HasSubst.single t m x)
      rw [Unifier.toSubst_cons_pSubst, ← habs]
      exact hrec
  | case8 _ _ _ _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]
  | case9 x y eqs' hxv hyv xs hdec ih =>
      intro u hu σ hσ
      have hu : unifyList (xs ++ eqs') = some u := by grind [unifyList]
      have hxy : Signature.pSubst x σ = Signature.pSubst y σ := Subst.Unifies.head_eq hσ
      have hσ' : Subst.Unifies σ (xs ++ eqs') := by
        intro p hp
        rcases List.mem_append.mp hp with hp_xs | hp_eqs'
        · exact Signature.decomp_unifier_sound x y xs σ hdec hxy p hp_xs
        · exact hσ p (List.mem_cons_of_mem _ hp_eqs')
      exact ih u hu σ hσ'
  | case10 _ _ _ _ _ _ => intro u hu _ _; grind [unifyList]

/-! ## Public MGU.

Both `unify_complete` (in `Completeness.lean`) and `unify_mgu` now quantify over an arbitrary
parallel `Subst A α`, which is the textbook notion of a unifier — any substitution making the
equations hold. There used to be a `Subst`→`Unifier` bridge here, `exists_equivalent_unifier`,
turning an arbitrary parallel substitution into a list with the same action. **That is
impossible**: `Unifier.toSubst` collapses a list by pushing the tail into each value, so its
image consists only of acyclic substitutions, and a cyclic one like `{0 ↦ ?1, 1 ↦ ?0}` has no
preimage. Since the inductions only ever used the *action* of the hypothetical unifier and never
its list structure, generalising them was both possible and simpler.
-/

/-- **Most-generality of `unify`.** When `unify eqs = some σ`, `σ` is at least as general as any
substitution unifying `eqs`. -/
theorem unify_mgu {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (σ : Subst A α),
      unify eqs = some σ →
      ∀ (σ' : Subst A α), Subst.Unifies σ' eqs →
      MoreGeneral σ σ' := by
  intro eqs σ hu σ' hσ'
  rw [unify, Option.map_eq_some_iff] at hu
  obtain ⟨u₁, hul, rfl⟩ := hu
  exact unifyList_mgu eqs u₁ hul σ' hσ'

/-- List-form corollary, mirroring `unify_complete_unifier`. -/
theorem unify_mgu_unifier {A α : Type} [Atom A] [Signature A α] :
    ∀ (eqs : Equations α) (σ : Subst A α),
      unify eqs = some σ →
      ∀ (u : Unifier A α), u.Unifies eqs →
      MoreGeneral σ u.toSubst := by
  intro eqs σ hu u hunif
  refine unify_mgu eqs σ hu u.toSubst (fun p hp => ?_)
  have h := hunif p hp
  rwa [Unifier.apply_eq_pSubst_toSubst, Unifier.apply_eq_pSubst_toSubst] at h

/-! ## The result of a most-general-unifier computation, as a type

`unify_unifies`, `unify_mgu` and `unify_complete` are three separate statements about the same
call. `MGUProp` is the type that holds whichever of them applies, so a caller pattern-matches once
instead of chaining an `Option` with two side lemmas — and cannot forget the negative case, since
it is a constructor rather than a `none`.

There are two such types, not one, and the split is the same one `TypeSystem` makes between the
bare class and `LawfulTypeSystem`. `SolutionProp` answers *whether* there is a solution, with a
witness or a proof of absence; `MGUProp` additionally claims the witness is **most general**.
Most-generality is a strictly harder obligation than the other two put together — for the STLC
elaborator it is the one remaining open problem — so demanding it in the same type makes a
decision procedure uninhabitable long after the decision itself is proved. Weaker type, no side
conditions: a caller that only needs "is this typeable, and by what" asks for `SolutionProp`, and
`MGUProp.toSolution` hands it one from anything stronger. -/

/-- A decision about `P` over substitutions, carrying evidence either way: a σ satisfying it, or a
proof that none does — but saying nothing about how that σ compares to other solutions.

No `HasSubst` instance is required, which is the point of separating this from `MGUProp`: with no
`MoreGeneral` in the statement there is nothing to substitute into, so `𝕊` may be any type at all.

`impossible` carries the same reading here as there: a *proof of absence*, never a failed search.
That is the entire content of this type over `Option (Subst A 𝕊)`, and the reason a procedure
returning it cannot quietly answer "I gave up". -/
inductive SolutionProp {A 𝕊 : Type} [Atom A] (P : Subst A 𝕊 → Prop) where
  /-- A σ satisfying `P`. -/
  | solution (σ : Subst A 𝕊) (hσ : P σ) : SolutionProp P
  /-- No σ satisfies `P`. -/
  | impossible (h : ∀ σ, ¬ P σ) : SolutionProp P

/-- The substitution a decision found, if it found one.

Exists so that a *law* about a `SolutionProp`-valued field can be stated without naming the
constructor's proof argument: `d.subst? = some σ → …` quantifies over the σ alone, whereas
`d = .solution σ hσ` drags an existential over `hσ` along with it. This is what
`TypeSystem.Named.PrincipalElaborate` uses to add most-generality on top of a decision rather than
inside it. -/
def SolutionProp.subst? {A 𝕊 : Type} [Atom A] {P : Subst A 𝕊 → Prop} : SolutionProp P → Option (Subst A 𝕊)
  | .solution σ _ => some σ
  | .impossible _ => none

/-- Whatever `subst?` returns satisfies `P` — the positive half, recovered after the proof
argument has been projected away. -/
theorem SolutionProp.holds_of_subst? {A 𝕊 : Type} [Atom A] {P : Subst A 𝕊 → Prop} :
    ∀ (d : SolutionProp P) {σ : Subst A 𝕊}, d.subst? = some σ → P σ
  | .solution _ hσ, _, h => by cases Option.some.inj h; exact hσ

/-- `subst? = none` is a proof of absence — the negative half, likewise recovered. -/
theorem SolutionProp.not_of_subst?_none {A 𝕊 : Type} [Atom A] {P : Subst A 𝕊 → Prop} :
    ∀ (d : SolutionProp P), d.subst? = none → ∀ σ, ¬ P σ
  | .impossible h, _ => h

/-- The decidability the type is named for. Strictly weaker than the type itself: `isTrue` carries
no extractable σ, since `∃` lives in `Prop`. -/
def SolutionProp.decidable {A 𝕊 : Type} [Atom A] {P : Subst A 𝕊 → Prop} :
    SolutionProp P → Decidable (∃ σ, P σ)
  | .solution σ hσ => .isTrue ⟨σ, hσ⟩
  | .impossible h => .isFalse (fun ⟨σ, hσ⟩ => h σ hσ)

/-- A decision about `P` over substitutions, carrying evidence either way: the **most general** σ
satisfying it, or a proof that none does. `MoreGeneral σ σ'` says every competing solution factors
through σ — there is a τ with `pSubst t σ' = pSubst (pSubst t σ) τ` for all `t`.

Both constructors name *what is the case*, never how it was established. That is deliberate:
`Subst A 𝕊` is infinite, so `impossible` can never come from enumeration — it comes from unification
failing structurally, on an occurs check or a rigid-rigid clash. Any name suggesting an exhaustive
search would be wrong in exactly the case this type exists for. `impossible` is likewise a *proof
of absence*, not a failure to find one; that distinction is the whole content of this type over
`Option`.

Strictly stronger than `Decidable (∃ σ, P σ)`, which is why it is worth writing down: the map
`MGUProp P → Decidable (∃ σ, P σ)` is definable, the converse is not, because `∃` lives in `Prop`
and `isTrue` therefore carries no extractable σ. `𝕊` is implicit, being determined by `P`. -/
inductive PrincipalProp {A 𝕊 : Type} [Atom A] (R : Subst A 𝕊 → Subst A 𝕊 → Prop) (P : Subst A 𝕊 → Prop) where
  /-- A σ satisfying `P` that every other solution factors through, in the sense of `R`. -/
  | mgu (σ : Subst A 𝕊) (hσ : P σ) (hmgu : ∀ σ', P σ' → R σ σ') : PrincipalProp R P
  /-- No σ satisfies `P`. -/
  | impossible (h : ∀ σ, ¬ P σ) : PrincipalProp R P

/-- **The unification instance**: most general in the full `MoreGeneral` sense, which is the right
comparison here — `unify`'s answer is compared against other *unifiers of the same equations*, and
those speak about every variable the equations mention.

An elaborator cannot ask for this: it draws variables its caller never mentioned, and a competing
solution says nothing about them (`Stlc/Named/Typing/Principality.lean` proves the resulting
statement false). That is why the comparison is a parameter and not baked in — see
`TypeSystem.Named.PrincipalElaborate`, which instantiates it at `MoreGeneralBelow`. -/
abbrev MGUProp {A 𝕊 : Type} [Atom A] [HasSubst A 𝕊 𝕊] (P : Subst A 𝕊 → Prop) : Type :=
  PrincipalProp MoreGeneral P

/-- Forget most-generality. The converse is not definable, which is what makes the split worth
having: everything proved about `SolutionProp` applies to an `MGUProp` for free, and nothing that
merely decides has to pretend to more. -/
def PrincipalProp.toSolution {A 𝕊 : Type} [Atom A] {R : Subst A 𝕊 → Subst A 𝕊 → Prop} {P : Subst A 𝕊 → Prop} :
    PrincipalProp R P → SolutionProp P
  | .mgu σ hσ _ => .solution σ hσ
  | .impossible h => .impossible h

/-- **`unify` packaged as an `MGUProp`.** Both constructors come out of theorems already proved
here: success gives `unify_unifies` and `unify_mgu`, and failure gives the contrapositive of
`unify_complete` — if any σ unified, `unify` could not have returned `none`.

This is the intended inhabitant, and the reason the type is stated over an arbitrary predicate
rather than over `Subst.Unifies` directly: `Stlc/Named/Typing/Target.lean` wants the same shape
for the typing predicate, where the `impossible` branch is still open. -/
def unifyMGU {A α : Type} [Atom A] [Signature A α] (eqs : Equations α) :
    MGUProp (fun σ : Subst A α => Subst.Unifies σ eqs) :=
  match h : unify eqs with
  | some σ => .mgu σ (unify_unifies eqs σ h) (fun σ' hσ' => unify_mgu eqs σ h σ' hσ')
  | none => .impossible (fun σ hσ => unify_complete eqs σ hσ h)

