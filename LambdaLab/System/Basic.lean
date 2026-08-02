
structure TypeSystem where
  Tm : Type
  Ty : Type

  HasType : Ctx Ty → Tm → Ty → Prop
