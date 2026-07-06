import LambdaLab.ParserOld.Basic

namespace LambdaLab.Language1

open LambdaLab.ParserOld

structure Language where
  Tm : Type
  Ty : Type

  pTm : LambdaLab.ParserOld.TruncatingParser Token Tm
  pTy : LambdaLab.ParserOld.TruncatingParser Token Ty

end LambdaLab.Language1
