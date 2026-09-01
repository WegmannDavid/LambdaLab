import LambdaLab.CoC.Named.Typing.Basic

/-!
# Named CoC claims the named tower — one carrier, both slots, one alphabet

The mirror of `CoC/DeBruijn/TypeSystem.lean`'s claim: `(N, Term N, Term N)`. Note what the
collapse spares us relative to named System F: no second alphabet riding along, and — once the
translation exists — the bridge's single-alphabet erasure applies as-is, where F needs the
interface generalized first. CoC is the dependent calculus that *fits* the existing bridge.

Lawless floor only; the road up is `CoC/DeBruijn/TypeSystem.lean`'s (confluence before
preservation, SN at the summit) plus the named layer's own α-machinery and translation, with
the shadowing question its `Typing/Basic.lean` header records awaiting the audit.
-/

namespace LambdaLab.CoC.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-- The judgement, claimed — one carrier in both slots. -/
instance instHasType : TypeSystem.Named.HasType N (Term N) (Term N) where
  HasType := HasType

/-- Judgement and reduction together. -/
instance instTypeSystem : TypeSystem.Named.TypeSystem N (Term N) (Term N) := {}

end LambdaLab.CoC.Named
