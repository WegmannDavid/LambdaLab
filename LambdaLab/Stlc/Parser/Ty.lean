
namespace Stlc.Parser

inductive Ty : Type where
| atm : String → Ty
| inf : Ty
| arr : Ty → Ty → Ty
deriving DecidableEq


instance : ToString Ty where
  toString :=
    let rec h t :=
      match t with
      | .atm s    => s
      | .inf      => s!"?"
      | .arr α β  => s!"({h α} → {h β})"
    h

end Stlc.Parser
