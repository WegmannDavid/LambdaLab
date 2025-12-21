import LambdaLab.CoC.Tm

abbrev Declaration := String × Tm × Tm

instance : ToString Declaration where
  toString := λ ⟨ s, α, t ⟩ ↦  s!"def {s} : {α} := {t};\n"

abbrev Vernacular := List Declaration

instance : ToString Vernacular where
  toString := let rec h (l : Vernacular) :=
    match l with
    | []    => s!"end of file"
    | d::ds => toString d ++ h ds
    h
