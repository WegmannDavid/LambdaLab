import LambdaLab.SysF.DeBruijn.Typing.Basic
import LambdaLab.SysF.DeBruijn.Step.Basic
import LambdaLab.TypeSystem.DeBruijn.Basic

/-!
# System F claims the de Bruijn tower — the lawless floor, honestly

The judgement and the reduction, and nothing above them: the tower's opt-in doctrine is that a
system instantiates the classes it satisfies and no more, and today System F satisfies exactly
the lawless ones. What each next floor will cost, recorded now:

* `LawfulTypeSystem` — preservation. The substitution lemma doubles: term-substitution typing
  (as STLC's, with the `tlam` crossing) *and* type-substitution typing (`tsubst` against the
  context's `Ty.subst` — the commutation of `Ty.subst` with `Ty.shift` is the new arithmetic).
* `LawfulMVars` — trivial by design: `Ty` has no `mvar`, so metavariable substitution is the
  identity and every law is near-`rfl`. The `Basic.lean` header says why the constructor was
  left out; this is the payoff.
* `Confluent` — the parallel-reduction argument again, now with two β's interacting.
* `StronglyNormalizing` — **Girard's reducibility candidates**: the famous impredicative
  argument, and the single largest piece of metatheory this repository will have attempted.
  It is the reason System F was worth adding, and it gets its own arc.
-/

namespace LambdaLab.SysF.DeBruijn

/-- The judgement, claimed: `Ctx` *is* the tower's `Context Ty`. -/
instance instHasType : TypeSystem.DeBruijn.HasType Term Ty where
  HasType := HasType

/-- Judgement and reduction together — `Step/Basic.lean`'s `instStep` supplies the other half. -/
instance instTypeSystem : TypeSystem.DeBruijn.TypeSystem Term Ty := {}

end LambdaLab.SysF.DeBruijn
