import LambdaLab.ParserOld.Basic
import LambdaLab.ParserOld.Token

namespace LambdaLab.ParserOld

--abbrev Token (sep : Char → Bool) := (Restricted (λ s => ∀ c, sep c → c ∉ s))

--def tokenize (sep : Char → Bool) : TruncatingParser Char (List (Token sep)) := sorry

end LambdaLab.ParserOld
