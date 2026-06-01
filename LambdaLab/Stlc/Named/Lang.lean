import LambdaLab.Stlc.Named.W
import LambdaLab.Stlc.Named.Eval
import LambdaLab.Language.Basic

/-!
# `Language` instance for named STLC

Bundles the named-STLC syntax, typing relation, verified inferrer, and
verified normalizer into a single `Language` value.

The `eval` field is currently a stub that returns its input verbatim.
Real evaluation needs the bridge preconditions (`Γ.Ground`,
`e.AnnotsGround`) which the kernel `HasType` doesn't carry. Once the
elaborator is in place, this stub will be replaced with one that
threads the elaborator's well-formedness witnesses through to
`HasType.eval`.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language

/-- Placeholder: returns the input term. To be replaced by
`HasType.eval` once the elaborator threads `Ground`/`AnnotsGround`
witnesses through. -/
private def evalStub {Γ : Ctx} {e : Term} {τ : Ty}
    (_ : HasType Γ e τ) : Term := e

/-- The canonical `Language` for named STLC. -/
def lang : Language where
  Ty := Ty
  Term := Term
  tyDecEq := inferInstance
  tyHasSubst := inferInstance
  freshTy := Ty.mvar
  tyPSubstEmpty := Signature.pSubst_empty
  termHasSubst := inferInstance
  HasType := HasType
  elaborate := Term.elaborate
  eval := evalStub

end LambdaLab.Stlc.Named
