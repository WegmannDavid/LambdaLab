import LambdaLab.Language1.Context
import LambdaLab.Substitution.Basic

/-!
# Elaboration results, parametric in the name alphabet

Copied from `Language/Basic.lean` — the reference interface — and generalized so that contexts
are keyed by a language's own variable names (`Var L`) rather than by `String`.

## Why a substitution comes along

The obvious lighter interface, "infer a type, with a derivation":

```lean
elaborate : (Γ) → (e) → Option (Σ τ, HasType Γ e τ)
```

is **wrong for Hindley–Milner**, and it is worth saying why, because five of the fields below
exist only for this reason. `W` does not establish `HasType Γ e τ`; it establishes that some
substitution *makes* the triple type. There is no way to get the un-substituted judgement back
out — the metavariables in `Γ` and `τ` may genuinely need solving. So the witness carries the
`σ`, and `HasSubst` on types, terms and contexts is forced by inference itself rather than
inherited as ceremony.

`mgu` is what makes the result *principal*: any other substitution that types the triple is less
general. That is the content `W_principal` is meant to supply.
-/

namespace LambdaLab.Language1

variable {N : Type} [NameAlphabet N]

/-- `τ` is a *principal* type for `e` under `Γ`: a witness substitution `σ` that types the
triple, together with the claim that every other typing substitution factors through it. -/
structure Elaboration {Ty Tm : Type}
    [HasSubst Ty Ty] [HasSubst Tm Ty] [HasSubst (Context N Ty) Ty]
    (HasType : Context N Ty → Tm → Ty → Prop)
    (Γ : Context N Ty) (e : Tm) (τ : Ty) : Type where
  σ : Subst Ty
  hSat : HasType (HasSubst.pSubst Γ σ) (HasSubst.pSubst e σ) (HasSubst.pSubst τ σ)
  mgu : ∀ σ' : Subst Ty,
          HasType (HasSubst.pSubst Γ σ') (HasSubst.pSubst e σ') (HasSubst.pSubst τ σ') →
          MoreGeneral σ σ'

/-- The result of elaborating `e` against `τ`: a principal-type witness, or a refutation that
there is one. The error branch carries no diagnostic — see the note in `Language/Check.lean`. -/
inductive ElaborationResult {Ty Tm : Type}
    [HasSubst Ty Ty] [HasSubst Tm Ty] [HasSubst (Context N Ty) Ty]
    (HasType : Context N Ty → Tm → Ty → Prop)
    (Γ : Context N Ty) (e : Tm) (τ : Ty) : Type where
  | error : (Elaboration HasType Γ e τ → False) → ElaborationResult HasType Γ e τ
  | ok    : Elaboration HasType Γ e τ → ElaborationResult HasType Γ e τ

/-! ## Trivial typing

A language with no typing discipline — or one whose real elaborator is not yet wired up — still
has to fill the semantic fields. These make that cheap: nothing is a metavariable, so
substitution is the identity, every term has every type, and elaboration always succeeds with the
empty substitution (which is vacuously most general, since every substitution acts as identity).
-/

/-- No metavariables: substitution is the identity. -/
def trivialHasSubst (α β : Type) : HasSubst α β where
  isFree _ _ := False
  fresh _ := 0
  fresh_gt_free := fun _ _ h => h.elim
  pSubst t _ := t

/-- With `trivialHasSubst`, the empty substitution is most general — everything acts as the
identity, so any `σ'` is matched by taking `τ = ∅`. -/
theorem trivial_moreGeneral {α : Type} [inst : HasSubst α α]
    (hid : ∀ (t : α) (σ : Subst α), HasSubst.pSubst t σ = t) (σ σ' : Subst α) :
    MoreGeneral σ σ' :=
  ⟨∅, fun t => by rw [hid t σ', hid (HasSubst.pSubst t σ) ∅, hid t σ]⟩

end LambdaLab.Language1
