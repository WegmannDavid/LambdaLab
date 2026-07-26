
structure Abstraction (Concrete Abstract : Type) (Annotation : Abstract → Type) where
  abstract : Concrete → Abstract
  realize : (a : Abstract) → (Annotation a) → Concrete
  default : (a : Abstract) → Annotation a

  abstract_realize : ∀ (a : Abstract) (ann : Annotation a), abstract (realize a ann) = a
