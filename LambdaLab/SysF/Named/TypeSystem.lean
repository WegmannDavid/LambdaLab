import LambdaLab.SysF.Named.Typing.Basic
import LambdaLab.SysF.Named.Step.Basic

/-!
# Named System F claims the named tower — the lawless floor

The mirror of `SysF/DeBruijn/TypeSystem.lean`'s claim, at the named tower: judgement and
reduction, instantiated at `(N, Term N TN, Ty TN)` with the type-name alphabet riding along as
an ordinary parameter the interface never sees.

The frontier from here, in dependency order: the α-machinery and the translation to
`SysF/DeBruijn` (two binder kinds now, so the erasure is relative to *two* scopes — which the
bridge interface, built single-alphabet, cannot yet express; generalizing `HasErase` to a
richer scope type is the recorded prerequisite for a System F bridge instance), then the
lawful floors ride the generalized bridge as STLC's do.
-/

namespace LambdaLab.SysF.Named

open LambdaLab.Nominal (Atom)

variable {N TN : Type} [Atom N] [Atom TN]

/-- The judgement, claimed. -/
instance instHasType : TypeSystem.Named.HasType N (Term N TN) (Ty TN) where
  HasType := HasType

/-- Judgement and reduction together — `Step/Basic.lean`'s `instStep` supplies the other
half. -/
instance instTypeSystem : TypeSystem.Named.TypeSystem N (Term N TN) (Ty TN) := {}

end LambdaLab.SysF.Named
