import LambdaLab.TypeSystem.Named.Vernacular.Basic
import LambdaLab.TypeSystem.Named.Basic

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

## Everything is ground

A declaration may not leave a metavariable behind — neither in its declared type nor anywhere in
its body — and neither may the context it is checked against. That is a real restriction, and it
is what the judgement's name records.

**Why.** A declaration is a *commitment*: its type is entered into the context and every later
declaration is checked against it. An unsolved metavariable there is not something the vernacular
can hold onto — it is a hole that later declarations would each be free to fill differently, and
the context would no longer describe one program. Inference happens during elaboration; by the
time a command is accepted, the answer has to have been found.

**How.** Groundness is `HasVars.Ground` — no free metavariable — stated over `HasVars`, the
smallest class that can say it. Deliberately *not* over `MVars` or the rest of the `TypeSystem`
tower: nothing here substitutes, so nothing here should demand a substitution operation, let alone
a reduction relation.

For STLC this is exactly the condition the pipeline already enforces. `HasVars (Term N)`'s
`isFree` is `Term.tyIsFree`, so `Ground t` says no annotation inside `t` mentions a metavariable —
the `AnnotsGround` conjunct of `Stlc/Named/Pipeline.lean`'s `solve` — and `Ground τ` is its
`Ground` conjunct. The vernacular's rule and the elaborator's refusal to let a metavariable
survive a declaration are the same rule, now stated once and generically.

## What a declaration contributes

`decl x τ t` extends the context with `x : τ` — the *declared* type, not something inferred from
`t`. The two agree, since the same `τ` is what `t` is checked against; taking the declared one
keeps the judgement readable and keeps the context independent of how the type was arrived at.

`Context.cons` is `insert`, so a redeclared name **shadows** rather than colliding. That is a
deliberate choice inherited from the context type: this judgement says nothing about uniqueness of
declaration names, and a vernacular wanting to reject shadowing states it separately rather than
by making well-typedness fail.
-/

namespace LambdaLab.TypeSystem.Named.Vernacular

open HasVars (Ground)
open LambdaLab.Nominal (Atom)

/-! `HasType` below is the *program*-level judgement, and it shares its name with the object
language's class in the parent namespace. Both are wanted under those names, so every reference to
the class is qualified: an unqualified one in a statement written after the `abbrev` resolves to
the program-level judgement and fails with an arity mismatch. -/

variable {N Tm Ty : Type} [Atom N] [_root_.LambdaLab.TypeSystem.Named.HasType N Tm Ty]
  [HasVars Tm] [HasVars Ty]

/-- Every type bound in `Γ` is ground.

Declared before the judgement because `nil` demands it: the context is as much a part of "ground"
as the declarations are. -/
def CtxGround (Γ : Context N Ty) : Prop := ∀ (x : N) (τ : Ty), Γ.get? x = some τ → Ground τ

/-- **Ground declarations typed in a ground context**, starting from `Γ`.

`HasTypeGround Γ cs` says: check the head against `Γ` and confirm it left no metavariable behind,
then check the rest against `Γ` extended with the head's name and declared type, and so on to the
end of the list — where the context, too, holds nothing but ground types.

## Why the context condition sits on `nil`

Stating it once suffices, and `nil` is the one place it must be stated. The `decl` rule only ever
extends the context with a `τ` it has just required to be ground, so it cannot *introduce* a hole;
`nil` is where the accumulated context is finally exposed with nothing left to check it against.
Putting the condition there means every rule is either preserving groundness or asserting it, and
none of them repeats it.

Note what this does **not** give: `HasTypeGround Γ cs → CtxGround Γ` is false, and not by
oversight. `decl` may *shadow* — a `Γ` binding `y : ?0` extended with `y : ⋆` is ground although
`Γ` was not — so groundness of a later context says nothing about an earlier one. What holds is
the direction that matters: start ground and you stay ground (`CtxGround.empty`, `CtxGround.cons`
below), which is exactly the situation `HasType` sets up. -/
inductive HasTypeGround : Context N Ty → List (Command N Tm Ty) → Prop where
  /-- Nothing left to declare — and the context reached holds no metavariable. -/
  | nil {Γ : Context N Ty} : CtxGround Γ → HasTypeGround Γ []
  /-- `def x : τ := t` is well-typed here when `t` has type `τ` here and neither is left holding a
  metavariable — and the declarations after it are well-typed in the context that `x : τ` has been
  added to. -/
  | decl {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm} {cs : List (Command N Tm Ty)} :
      _root_.LambdaLab.TypeSystem.Named.HasType.HasType Γ t τ → Ground τ → Ground t →
      HasTypeGround (Γ.cons x τ) cs →
      HasTypeGround Γ (Command.decl x τ t :: cs)

/-- **A well-typed program**: its declarations type in sequence from the empty context, and none
of them leaves a metavariable behind.

`p.toList` is `p.head :: p.tail`, so the head is the declaration checked against `Context.empty`
— a program's first declaration may refer to nothing but itself. -/
abbrev HasType (p : Program N Tm Ty) : Prop :=
  HasTypeGround (Context.empty : Context N Ty) p.toList

/-! ## Groundness is an invariant, not only a per-declaration check

The judgement demands a ground type at each declaration and a ground context at the end; these two
are what carry that from one to the other. `empty` starts the induction and `cons` is its step, so
a derivation begun at `Context.empty` discharges `nil`'s condition by construction rather than by
a separate argument. -/

theorem CtxGround.empty : CtxGround (Context.empty : Context N Ty) := by
  intro x τ hx
  rw [Context.get?_empty] at hx
  exact absurd hx (by simp)

theorem CtxGround.cons {Γ : Context N Ty} {x : N} {τ : Ty}
    (h : CtxGround Γ) (hτ : Ground τ) : CtxGround (Γ.cons x τ) := by
  intro y σ hy
  rw [Context.get?_cons] at hy
  split at hy
  · exact Option.some.inj hy ▸ hτ
  · exact h y σ hy

/-- **The payoff**: in a well-typed sequence *every* declaration is ground, not merely the one the
derivation happens to be looking at. -/
theorem HasTypeGround.ground_of_mem {Γ : Context N Ty} {cs : List (Command N Tm Ty)}
    (h : HasTypeGround Γ cs) :
    ∀ {x : N} {τ : Ty} {t : Tm}, Command.decl x τ t ∈ cs → Ground τ ∧ Ground t := by
  induction h with
  | nil _ => intro x τ t hmem; cases hmem
  | decl _ hτ ht _ ih =>
      intro y σ s hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · cases heq; exact ⟨hτ, ht⟩
      · exact ih hmem'

/-- The same, over a program rather than its list of commands. -/
theorem HasType.ground_of_mem {p : Program N Tm Ty} (h : HasType p)
    {x : N} {τ : Ty} {t : Tm} (hmem : Command.decl x τ t ∈ p.toList) : Ground τ ∧ Ground t :=
  HasTypeGround.ground_of_mem h hmem

/-! ## The two cases, unfolded -/

/-- A singleton program is well-typed exactly when its body checks against its declared type in
the empty context, with neither carrying a metavariable. -/
theorem hasType_singleton {x : N} {τ : Ty} {t : Tm} :
    HasType (NEList.singleton (Command.decl x τ t)) ↔
      _root_.LambdaLab.TypeSystem.Named.HasType.HasType (Context.empty : Context N Ty) t τ
        ∧ Ground τ ∧ Ground t := by
  constructor
  · intro h
    cases h with
    | decl hty hτ ht _ => exact ⟨hty, hτ, ht⟩
  · intro ⟨hty, hτ, ht⟩
    exact .decl hty hτ ht (.nil (CtxGround.empty.cons hτ))

/-- Peeling the head: a program is well-typed exactly when its first declaration checks — and is
ground — in the empty context, and the rest check in the context that declaration extends. -/
theorem hasType_cons {x : N} {τ : Ty} {t : Tm} {cs : List (Command N Tm Ty)} :
    HasType (Command.decl x τ t, cs) ↔
      _root_.LambdaLab.TypeSystem.Named.HasType.HasType (Context.empty : Context N Ty) t τ
        ∧ Ground τ ∧ Ground t
        ∧ HasTypeGround ((Context.empty : Context N Ty).cons x τ) cs := by
  constructor
  · intro h
    cases h with
    | decl hty hτ ht hrest => exact ⟨hty, hτ, ht, hrest⟩
  · intro ⟨hty, hτ, ht, hrest⟩
    exact .decl hty hτ ht hrest

end LambdaLab.TypeSystem.Named.Vernacular
