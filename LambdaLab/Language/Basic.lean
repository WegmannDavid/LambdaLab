import LambdaLab.Substitution.Basic
import LambdaLab.Parser.Basic
import Std.Data.HashMap


/-!
# Language interface

A `Language` bundles the per-language hooks the vernacular needs:
a typing relation, an algorithmic inferrer, and an evaluator. Anything
that should work uniformly across object languages (type-checking,
evaluation) is parametric on this structure.

## Pinned design choices

* **Contexts are name-keyed hashmaps:** `Context Ty := Std.HashMap String Ty`.
  Shadowing is `insert` (overrides). De-Bruijn-style languages are not
  required to instance `Language`.
* **Inference returns a derivation.** `infer` produces a `CheckResult`
  whose `ok` constructor carries a proof in the language's `HasType`,
  so soundness is by construction.
* **Evaluation only operates on well-typed terms.** `eval` takes a
  derivation as input and returns a term; the obligation that "ill-typed
  terms shouldn't reduce" is discharged at the type level rather than
  by partiality.
-/

namespace LambdaLab.Language

/-! ## Contexts -/

/-- A typing context: a hashmap from variable names to types. -/
abbrev Context (Ty : Type) : Type := Std.HashMap String Ty

/-- The empty context. -/
def Context.empty {Ty : Type} : Context Ty := ∅

/-- Extend a context with a binding `x : τ`. The new binding shadows
any previous binding of `x`. -/
def Context.cons {Ty : Type} (x : String) (τ : Ty) (Γ : Context Ty) :
    Context Ty :=
  Γ.insert x τ

/-! ## Type-check results -/

/-- Errors that a type-checker can report. Parametric on the type
universe `Ty` so callers can attach the offending types directly. -/
inductive TypeError (Ty : Type) where
  | unbound  : String → TypeError Ty
  | notArrow : (actual : Ty) → TypeError Ty
  | mismatch : (expected actual : Ty) → TypeError Ty

/-- `Elaborable HasType Γ e τ` — `τ` is a *principal* type for `e`
under `Γ`. Bundles a witness substitution `σ` with proofs that:
* `σ` types the triple `(Γ, e, τ)` after pSubst;
* `σ` is more general than every other substitution that types the
  triple at `τ`.

The type `τ` is a parameter (no `∃ τ`); `σ` lives as a structure field
rather than an existential so callers can destructure it in
`Type`-valued definitions. -/
structure Elaboration {Ty Term : Type}
    [HasSubst Ty Ty] [HasSubst Term Ty] [HasSubst (Context Ty) Ty]
    (HasType : Context Ty → Term → Ty → Prop)
    (Γ : Context Ty) (e : Term) (τ : Ty) : Type where
  σ    : Subst Ty
  hSat : HasType (HasSubst.pSubst Γ σ)
                 (HasSubst.pSubst e σ)
                 (HasSubst.pSubst τ σ)
  mgu  : ∀ σ' : Subst Ty,
           HasType (HasSubst.pSubst Γ σ')
                   (HasSubst.pSubst e σ')
                   (HasSubst.pSubst τ σ') →
           MoreGeneral σ σ'

/-- Result of elaborating `e` under `Γ`. The `ok` branch carries the
inferred type `τ` and the `Elaborable Γ e τ` witness; the `error`
branch carries a structured `TypeError` plus a uniform negative claim
`∀ τ, ¬ Elaborable Γ e τ` (no type at all is a principal type for `e`). -/
inductive ElaborationResult {Ty Term : Type}
    [HasSubst Ty Ty] [HasSubst Term Ty] [HasSubst (Context Ty) Ty]
    (HasType : Context Ty → Term → Ty → Prop)
    (Γ : Context Ty) (e : Term) (τ : Ty) : Type where
  | error : (Elaboration HasType Γ e τ → False) →
            ElaborationResult HasType Γ e τ
  | ok    : Elaboration HasType Γ e τ →
            ElaborationResult HasType Γ e τ

/-! ## The language interface -/


/-- A complete object-language interface. Bundles syntax (`Ty`, `Term`),
the declarative typing relation (`HasType`), the algorithmic inferrer
(`elaborate`), and the evaluator (`eval`). -/
structure Language : Type 1 where
  /-- Types of the object language. -/
  Ty : Type
  /-- Terms of the object language. -/
  Term : Type
  /-- Decidable equality on types — needed by `infer` to compare types
  in the application case. -/
  tyDecEq : DecidableEq Ty
  /-- Type-into-type substitution: how to apply a `Subst Ty` to a `Ty`
  (typically derived from a `Signature Ty` instance). -/
  tyHasSubst : HasSubst Ty Ty
  /-- Construct a `Ty` mvar from a `Nat` index. Used by inferential
  callers (`eval`/`check` commands) to pick a fresh type to feed into
  `elaborate`. -/
  freshTy : Nat → Ty
  /-- The empty substitution acts as the identity on `Ty`. Required to
  discharge the MGU witness in `ElaborateResult.ok` when the kernel
  picks `σ = ∅`. Typically `Signature.pSubst_empty`. -/
  tyPSubstEmpty : ∀ t : Ty, HasSubst.pSubst t (∅ : Subst Ty) = t
  /-- Substituting `Ty`-metavariables inside a `Term` (replaces type
  annotations). -/
  termHasSubst : HasSubst Term Ty
  /-- The declarative typing relation. -/
  HasType : Context Ty → Term → Ty → Prop
  /-- Bidirectional elaboration: fit `e` at the (possibly mvar-laden)
  expected type `τ` under `Γ`, returning a substitution `σ` that closes
  the existentials so `HasType` derives on the substituted triple. For
  full inference, pass a fresh `Ty.mvar` as `τ`; the returned `σ` then
  tells you what that mvar should be. -/
  elaborate : (Γ : Context Ty) → (e : Term) → (τ : Ty)→
          @ElaborationResult Ty Term tyHasSubst termHasSubst
            (by infer_instance) HasType Γ e τ
  /-- Evaluate a well-typed term. Taking the derivation as input keeps
  this function total — only well-typed terms are reducible. -/
  eval : ∀ {Γ : Context Ty} {e : Term} {τ : Ty}, HasType Γ e τ → Term

  pTy : Parser.LosslessParser Token Ty
  pTerm : Parser.LosslessParser Token Term

attribute [instance] Language.tyDecEq Language.tyHasSubst Language.termHasSubst

end LambdaLab.Language
