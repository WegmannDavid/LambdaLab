import LambdaLab.Parser.Basic

namespace LambdaLab.Language1

open LambdaLab.Parser

structure Language where
  Tm : Type
  Ty : Type

  pTm : LambdaLab.Parser.TruncatingParser Token Tm
  pTy : LambdaLab.Parser.TruncatingParser Token Ty

end LambdaLab.Language1
