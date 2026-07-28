import LambdaLab.Language1.Elaboration
import LambdaLab.Language1.Basic

/-!
# `ElaboratableLanguage` — a language that can also be type-checked

A `Language` says how to *read and print* a program. This says how to *give it meaning*: a
typing relation, and an algorithm that decides it.

It is a separate structure rather than extra fields on `Language`, because a language may be
parse-only — `arithLanguage` has no typing relation at all, and forcing it to invent one would be
a lie. `extends` says the right thing: every elaboratable language is a language, not the
converse.

Contexts are keyed by `Var` — the language's *own* variable names, which are also its declaration
names — so a parsed `def f : T := e` extends the context with `f` directly, with no injection
between two kinds of name.

## Status: no instances yet

The fields are stated against `Term`/`Ctx` shapes that STLC cannot currently supply: its
`HasType`, `W` and `Term.elaborate` are still pinned to `Term String` and a `String`-keyed `Ctx`.
Parameterizing those in the name alphabet — the same treatment `Term` itself received — is the
single remaining prerequisite. This file exists so that work has a target to hit.
-/

namespace LambdaLab.Language1

/-- A `Language` together with its semantics: types can be substituted into, terms have a typing
relation, and there is an elaborator deciding it. -/
structure ElaboratableLanguage extends Language where
  /-- Substituting metavariables inside a type. -/
  tyHasSubst : HasSubst Ty Ty
  /-- Substituting *type* metavariables inside a term (its annotations). -/
  tmHasSubst : HasSubst Tm Ty
  /-- …and inside a context. Taken as a field for the same reason the reference takes it as an
  instance argument: it is not derivable from the other two. -/
  ctxHasSubst : HasSubst (Context (Var toLanguage) Ty) Ty
  /-- Build a fresh type metavariable from an index. Callers that want full inference pass one of
  these as the expected type and read the answer out of the returned substitution. -/
  freshTy : Nat → Ty
  /-- The empty substitution acts as the identity on types. Needed to discharge the witness when
  the elaborator solves nothing. -/
  tyPSubstEmpty : ∀ t : Ty, HasSubst.pSubst t (∅ : Subst Ty) = t
  /-- The declarative typing relation. -/
  HasType : Context (Var toLanguage) Ty → Tm → Ty → Prop
  /-- The algorithm: fit `e` at the (possibly metavariable-laden) expected type `τ`, returning a
  principal-type witness or a refutation. -/
  elaborate : (Γ : Context (Var toLanguage) Ty) → (e : Tm) → (τ : Ty) →
    @ElaborationResult _ varAlphabet Ty Tm tyHasSubst tmHasSubst ctxHasSubst HasType Γ e τ
  /-- Evaluate a well-typed term. Taking the derivation as input keeps this total: only
  well-typed terms reduce. -/
  eval : ∀ {Γ : Context (Var toLanguage) Ty} {e : Tm} {τ : Ty},
    HasType Γ e τ → Tm

attribute [instance] ElaboratableLanguage.tyHasSubst ElaboratableLanguage.tmHasSubst
  ElaboratableLanguage.ctxHasSubst

/-! **Note on `tyDecEq`.** The reference interface carries a `DecidableEq Ty` field; this one does
not. Nothing in the interface needs it, and it is not always fillable computably — `arithLanguage`'s
`Ty` is a proof-carrying `Expr` tree with no derivable instance, so the field could only be
supplied classically, which would make the language noncomputable. A language whose elaborator
wants type equality can use it internally, as STLC's does. -/

end LambdaLab.Language1
