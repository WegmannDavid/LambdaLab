import LambdaLab.Parser.Mixfix.Basic
import LambdaLab.Substitution.Basic
import Std.Data.HashMap

/-!
# Language interface

A `Language` bundles the per-language hooks the vernacular needs:
sub-parsers for types and terms, a typing relation, an algorithmic
inferrer, and an evaluator. Anything that should work uniformly across
object languages (parsing, type-checking, evaluation) is parametric on
this structure.

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

open LambdaLab.Parser.Mixfix

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

/-- Result of elaborating `e` under `Γ`, where `Γ`, `e`, and the
inferred type may all carry existential type variables. Either a
structured error, or:

* an inferred type `τ`,
* an MGU `σ` that closes enough of those variables for the language's
  `HasType` relation to derive on the substituted triple, and
* a witness `mgu` that `σ` is more general than every other substitution
  that makes `(Γ, e, τ)` type-check.

`Subst Ty = HashMap Nat Ty` and the `pSubst` action are provided by the
`HasSubst _ Ty` instances. The kernel checker (which doesn't generate
mvars) uses `σ = ∅`, in which case the MGU witness is trivial (any other
σ' is more general than ∅ via `MoreGeneral σ' σ' = ⟨σ', …⟩`). -/
inductive ElaborateResult {Ty Term : Type}
    [HasSubst Ty Ty] [HasSubst Term Ty] [HasSubst (Context Ty) Ty]
    (HasType : Context Ty → Term → Ty → Prop)
    (Γ : Context Ty) (e : Term) : Type where
  | error : TypeError Ty → ElaborateResult HasType Γ e
  | ok    : (τ : Ty) → (σ : Subst Ty) →
            (hSat : HasType (HasSubst.pSubst Γ σ)
                            (HasSubst.pSubst e σ)
                            (HasSubst.pSubst τ σ)) →
            (mgu : ∀ σ' : Subst Ty,
              HasType (HasSubst.pSubst Γ σ')
                      (HasSubst.pSubst e σ')
                      (HasSubst.pSubst τ σ') →
              MoreGeneral σ σ') →
            ElaborateResult HasType Γ e

/-! ## The language interface -/

/-- A complete object-language interface. Bundles syntax (`Ty`, `Term`),
parsing (`typeParser` + printer, `termParser` + printer), the
declarative typing relation (`HasType`), the algorithmic inferrer
(`infer`), and the evaluator (`eval`). -/
structure Language : Type 1 where
  /-- Types of the object language. -/
  Ty : Type
  /-- Terms of the object language. -/
  Term : Type
  /-- State threaded through the language's sub-parsers (e.g. a fresh-
  mvar counter). `Unit` for stateless. -/
  ParserState : Type
  /-- The initial state value handed to a top-level parse. -/
  initialParserState : ParserState
  /-- Decidable equality on types — needed by `infer` to compare types
  in the application case. -/
  tyDecEq : DecidableEq Ty
  /-- Type-into-type substitution: how to apply a `Subst Ty` to a `Ty`
  (typically derived from a `Signature Ty` instance). -/
  tyHasSubst : HasSubst Ty Ty
  /-- The empty substitution acts as the identity on `Ty`. Required to
  discharge the MGU witness in `ElaborateResult.ok` when the kernel
  picks `σ = ∅`. Typically `Signature.pSubst_empty`. -/
  tyPSubstEmpty : ∀ t : Ty, HasSubst.pSubst t (∅ : Subst Ty) = t
  /-- Substituting `Ty`-metavariables inside a `Term` (replaces type
  annotations). -/
  termHasSubst : HasSubst Term Ty
  /-- The declarative typing relation. -/
  HasType : Context Ty → Term → Ty → Prop
  /-- Bidirectional elaboration: turn `(Γ, e)` (where `e` may carry
  unresolved type holes) into an inferred type, an MGU substitution,
  and a `HasType` derivation on the substituted triple. Intrinsically
  sound. -/
  elaborate : (Γ : Context Ty) → (e : Term) →
          @ElaborateResult Ty Term tyHasSubst termHasSubst
            (by infer_instance) HasType Γ e
  /-- Evaluate a well-typed term. Taking the derivation as input keeps
  this function total — only well-typed terms are reducible. -/
  eval : ∀ {Γ : Context Ty} {e : Term} {τ : Ty}, HasType Γ e τ → Term
  /-- Sub-parser for types (with bundled printer), plugged into the
  vernacular grammar. -/
  typeParser : Parser ParserState Ty
  /-- Sub-parser for terms (with bundled printer), plugged into the
  vernacular grammar. -/
  termParser : Parser ParserState Term

attribute [instance] Language.tyDecEq Language.tyHasSubst Language.termHasSubst

end LambdaLab.Language
