import LambdaLab.Language1.Vernacular
import LambdaLab.Parser.Basic
/-!
# Quick-and-dirty vernacular parser (parse only, unverified)

`Language.parser` parses a nonempty run of `def NAME : TYPE := BODY` commands,
delegating `TYPE` to `L.pTy` and `BODY` to `L.pTm` and taking the first parse of
each. `render` is a naive fully-spelled-out printer; `complete` (the round-trip)
is left as `sorry` — this is scaffolding, not a verified parser.
-/

namespace LambdaLab.Language1

def Language.parser (L : Language) : LambdaLab.Parser.TruncatingBiparser  Char (Program L) where

end LambdaLab.Language1
