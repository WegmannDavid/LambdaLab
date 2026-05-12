import LambdaLab.Parser.Mixfix.Basic
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

/-- Result of type-checking `e` under `Γ`: either a structured error,
or a type together with a derivation that `e` has that type. Parametric
on the language's `HasType` relation, so each `ok` carries the
language's own proof. -/
inductive CheckResult {Ty Term : Type}
    (HasType : Context Ty → Term → Ty → Prop)
    (Γ : Context Ty) (e : Term) : Type where
  | error : TypeError Ty → CheckResult HasType Γ e
  | ok    : (τ : Ty) → HasType Γ e τ → CheckResult HasType Γ e

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
  /-- Decidable equality on types — needed by `infer` to compare types
  in the application case. -/
  tyDecEq : DecidableEq Ty
  /-- The declarative typing relation. -/
  HasType : Context Ty → Term → Ty → Prop
  /-- Algorithmic type inference. The `ok` constructor of the result
  carries a `HasType` derivation, so this is intrinsically sound. -/
  infer : (Γ : Context Ty) → (e : Term) → CheckResult HasType Γ e
  /-- Evaluate a well-typed term. Taking the derivation as input keeps
  this function total — only well-typed terms are reducible. -/
  eval : ∀ {Γ : Context Ty} {e : Term} {τ : Ty}, HasType Γ e τ → Term
  /-- Sub-parser for types (with bundled printer), plugged into the
  vernacular grammar. -/
  typeParser : Parser Ty
  /-- Sub-parser for terms (with bundled printer), plugged into the
  vernacular grammar. -/
  termParser : Parser Term

attribute [instance] Language.tyDecEq

end LambdaLab.Language
