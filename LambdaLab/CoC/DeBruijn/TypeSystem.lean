import LambdaLab.CoC.DeBruijn.Typing.Basic
import LambdaLab.TypeSystem.DeBruijn.Basic

/-!
# CoC claims the de Bruijn tower — one carrier, both slots

The instantiation `Basic.lean` promised: `Tm := Term` **and** `Ty := Term`. The tower never
required the two to differ, and dependent types are the case where they don't — contexts are
`List Term`, the judgement is `Ctx → Term → Term → Prop`, and everything fits without a wrapper.
This is the structural answer to the two-level question System F raised: for the pipeline, one
parser entry instead of two; for the bridge, one alphabet and the existing single-scope erasure.

Lawless floor only, and the road up is steeper than F's, recorded honestly:

* `LawfulTypeSystem` — preservation for a dependent system needs the substitution lemma *and*
  conversion inversion (`Π`-injectivity up to `Conv`), which in turn wants **confluence first**:
  the metatheory order inverts relative to STLC.
* `Confluent` — parallel reduction / Takahashi again, one β this time.
* `StronglyNormalizing` — SN for CoC (Geuvers-style) is beyond even Girard's candidates; it is
  the summit of this repository's long game, and nothing below it blocks the pipeline work.
* `Conv`'s transitivity is also confluence's gift — `Step/Basic.lean` supplies `refl`/`symm`
  and deliberately not `trans`.
-/

namespace LambdaLab.CoC.DeBruijn

/-- The judgement, claimed — one carrier in both slots. -/
instance instHasType : TypeSystem.DeBruijn.HasType Term Term where
  HasType := HasType

/-- Judgement and reduction together. -/
instance instTypeSystem : TypeSystem.DeBruijn.TypeSystem Term Term := {}

end LambdaLab.CoC.DeBruijn
