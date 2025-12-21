import LambdaLab.Stlc.Tm


abbrev Declaration := String × Ty × Tm

instance : ToString Declaration where
  toString := λ ⟨ s, α, t ⟩ ↦  s!"\ndef {s} : {α} := {t};"

abbrev Vernacular := List Declaration

instance : ToString Vernacular where
  toString := let rec h (l : Vernacular) :=
    match l with
    | []    => s!"\nend of file"
    | d::ds => toString d ++ h ds
    h
