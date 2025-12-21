
namespace CoC.Parser

inductive Tm : Type where
| inf : Tm
| typ : Nat → Tm
| var : String → Tm
| app : Tm → Tm → Tm
| abs : String → Tm → Tm → Tm
| prd : String → Tm → Tm → Tm

instance : ToString Tm where
  toString :=
    let rec h t :=
      match t with
      | .inf       => s!"?"
      | .typ u     => s!"Type{u}"
      | .var x     => s!"{x}"
      | .app t s   => s!"({h t} {h s})"
      | .abs x α t => s!"λ {x} : {h α} . {h t}"
      | .prd x α t => s!"Π {x} : {h α} . {h t}"
    h

end CoC.Parser
