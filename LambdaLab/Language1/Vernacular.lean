import LambdaLab.Language1.Basic

namespace LambdaLab.Language1

inductive Command (L : Language) where
| decl  : LambdaLab.Parser.Token → L.Ty → L.Tm → Command L

abbrev Program (L : Language) := List (Command L)

end LambdaLab.Language1
