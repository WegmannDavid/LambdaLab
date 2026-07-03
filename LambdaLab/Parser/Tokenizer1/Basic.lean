import LambdaLab.Parser.Basic
import LambdaLab.Parser.Token

namespace LambdaLab.Parser

--abbrev Token (sep : Char → Bool) := (Restricted (λ s => ∀ c, sep c → c ∉ s))

--def tokenize (sep : Char → Bool) : TruncatingParser Char (List (Token sep)) := sorry

end LambdaLab.Parser
