import LambdaLab.Parser.Biparser

namespace LambdaLab.Language1

open LambdaLab.Parser
structure Language where
  Tm : Type
  Ty : Type

  pTm : LambdaLab.Parser.TruncatingBiparser Token Tm
  pTy : LambdaLab.Parser.TruncatingBiparser Token Ty

end LambdaLab.Language1
