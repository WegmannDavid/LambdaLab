import LambdaLab.Stlc.Parser.Ty

namespace Stlc.Parser

inductive Tm : Type where
| var : String → Tm
| app : Tm → Tm → Tm
| abs : String → Ty → Tm → Tm

instance : ToString Tm where
  toString :=
    let rec h t :=
      match t with
      | .var x    => s!"{x}"
      | .app t s  => s!"({h t} {h s})"
      | .abs x α t => s!"λ {x} : {α} . {h t}"
    h

end Stlc.Parser
