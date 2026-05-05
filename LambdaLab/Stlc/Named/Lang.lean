import LambdaLab.Stlc.Named.Check
import LambdaLab.Stlc.Named.Eval
import LambdaLab.Stlc.Named.Parser
import LambdaLab.Language.Basic

/-!
# `Language` instance for named STLC

Bundles the named-STLC syntax, typing relation, verified inferrer, and
verified normalizer into a single `Language` value. Anything parametric
on `Language` (the vernacular parser, `Decl`, `Program.check`, …) can
be specialised to STLC by passing `stlcLang`.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Language LambdaLab.Stlc.Named.Parser

/-- The canonical `Language` for named STLC. -/
def lang : Language where
  Ty := Ty
  Term := Term
  tyDecEq := inferInstance
  HasType := HasType
  infer := Term.infer
  eval := HasType.eval
  typeParser := typeParser
  termParser := termParser

end LambdaLab.Stlc.Named
