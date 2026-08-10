import LambdaLab.TypeSystem.Basic
import LambdaLab.NEList

namespace LambdaLab.TypeSystem.Vernacular

inductive Command (N Tm Ty : Type) where
| decl : N → Ty → Tm → Command N Tm Ty

abbrev Program (N Tm Ty : Type) := NEList (Command N Tm Ty)

end LambdaLab.TypeSystem.Vernacular
