
structure Abstraction (Concrete Abstract : Type) (Annotation : Abstract → Type) where
  abstract : Concrete → Abstract
  realize  : Annotation a → Concrete
  default : Annotation a

  abstract_realize : ∀ (a : Abstract) (a' : Annotation a), abstract (realize a') = a
  realize_complete : ∀ c, ∃ (a : Annotation (abstract c)), realize a = c
