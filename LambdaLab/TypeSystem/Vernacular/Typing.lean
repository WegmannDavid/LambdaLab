import LambdaLab.TypeSystem.Vernacular.Basic
import LambdaLab.TypeSystem.Basic

/-!
# When a program is well-typed

A `Command` is `def x : τ := t`, and a `Program` is one or more of them. Typing a program is
typing each declaration in turn, in the context its predecessors built: the first sees nothing,
the second sees the first's name at its declared type, and so on.

## The context is an index, not a parameter

It has to be. A parameter is fixed across all constructors, and the whole content of this
judgement is that the context *changes* as the list is consumed. So the recursion runs over a
`Context`-indexed relation on the command list, and `HasType` below pins the starting context to
the empty one — which is what "the first declaration sees nothing" means.

That also explains the split into two declarations rather than one. `Program` is a `NEList`, i.e.
a head paired with a possibly-empty tail, and the tail is an ordinary `List`; the accumulation
is a statement about lists, and non-emptiness has nothing to do with it.

## What a declaration contributes

`decl x τ t` extends the context with `x : τ` — the *declared* type, not something inferred from
`t`. The two agree, since the same `τ` is what `t` is checked against; taking the declared one
keeps the judgement readable and keeps the context independent of how the type was arrived at.

`Context.cons` is `insert`, so a redeclared name **shadows** rather than colliding. That is a
deliberate choice inherited from the context type: this judgement says nothing about uniqueness of
declaration names, and a vernacular wanting to reject shadowing states it separately rather than
by making well-typedness fail.
-/

namespace LambdaLab.TypeSystem.Vernacular

/-! `HasType` below is the *program*-level judgement, and it shares its name with the object
language's class in the parent namespace. Both are wanted under those names, so every reference to
the class is qualified: an unqualified one in a statement written after the `abbrev` resolves to
the program-level judgement and fails with an arity mismatch. -/

variable {N Tm Ty : Type} [NameAlphabet N] [_root_.LambdaLab.TypeSystem.HasType N Tm Ty]

/-- **Declarations typed in sequence**, starting from `Γ`.

`HasTypeFrom Γ cs` says: check the head against `Γ`, then check the rest against `Γ` extended
with the head's name and declared type, and so on to the end of the list. -/
inductive HasTypeFrom : Context N Ty → List (Command N Tm Ty) → Prop where
  /-- Nothing left to declare. Every context types the empty list. -/
  | nil {Γ : Context N Ty} : HasTypeFrom Γ []
  /-- `def x : τ := t` is well-typed here when `t` has type `τ` here — and the declarations after
  it are well-typed in the context that `x : τ` has been added to. -/
  | decl {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm} {cs : List (Command N Tm Ty)} :
      _root_.LambdaLab.TypeSystem.HasType.HasType Γ t τ → HasTypeFrom (Γ.cons x τ) cs →
      HasTypeFrom Γ (Command.decl x τ t :: cs)

/-- **A well-typed program**: its declarations type in sequence from the empty context.

`p.toList` is `p.head :: p.tail`, so the head is the declaration checked against `Context.empty`
— a program's first declaration may refer to nothing but itself. -/
abbrev HasType (p : Program N Tm Ty) : Prop :=
  HasTypeFrom (Context.empty : Context N Ty) p.toList

/-- The one-declaration case, unfolded: a singleton program is well-typed exactly when its body
checks against its declared type in the empty context. -/
theorem hasType_singleton {x : N} {τ : Ty} {t : Tm} :
    HasType (NEList.singleton (Command.decl x τ t)) ↔
      _root_.LambdaLab.TypeSystem.HasType.HasType (Context.empty : Context N Ty) t τ := by
  constructor
  · intro h
    cases h with
    | decl ht _ => exact ht
  · intro ht
    exact .decl ht .nil

/-- Peeling the head: a program is well-typed exactly when its first declaration checks in the
empty context and the rest check in the context that declaration extends. -/
theorem hasType_cons {x : N} {τ : Ty} {t : Tm} {cs : List (Command N Tm Ty)} :
    HasType (Command.decl x τ t, cs) ↔
      _root_.LambdaLab.TypeSystem.HasType.HasType (Context.empty : Context N Ty) t τ ∧
        HasTypeFrom ((Context.empty : Context N Ty).cons x τ) cs := by
  constructor
  · intro h
    cases h with
    | decl ht hrest => exact ⟨ht, hrest⟩
  · intro ⟨ht, hrest⟩
    exact .decl ht hrest

end LambdaLab.TypeSystem.Vernacular
