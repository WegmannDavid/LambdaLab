import LambdaLab.TypedLanguage.Context

/-!
# `TypeSystem` — a named object language bundled with its metatheory

Where `NameAlphabet` fixes what a *name* is and `Context` what a *context* is, this fixes what a
*type system over them* is: terms, types, a typing judgement, a reduction relation, and the
theorem tying the two together.

The point of the bundle is that `Preservation` is a **field**. A `TypeSystem` cannot be built
without discharging it, so the structure is not a signature that implementations may or may not
satisfy — it is the theorem-carrying record, and anything downstream may use preservation without
re-proving or re-assuming it.

## The name parameter is a field, not a parameter

`N` is bundled, with its `NameAlphabet` instance alongside it:

```lean
structure TypeSystem where
  N : Type
  [nameAlphabet : NameAlphabet N]
  ...
```

rather than `structure TypeSystem (N : Type) [NameAlphabet N]`. This matches `Tm` and `Ty`, which
are already fields, and it is what lets a `TypeSystem` be passed around as one value — a family
indexed by `N` would force every consumer to carry `N` and its instance too. The cost is the
`attribute [instance]` line below, without which `Context S.N S.Ty` cannot elaborate.

## Scope

Deliberately minimal. Normalization, confluence and the elaboration side are *not* fields: they
hold for STLC but not for every system worth describing this way, and a field no instance can
discharge is a field that keeps instances from existing. Preservation is the one property general
enough to demand of everything here.
-/

namespace LambdaLab.TypedLanguage

/-- A named object language together with the metatheory that makes it well-behaved: typing,
reduction, and a proof that reduction preserves types. -/
structure TypeSystem where
  /-- The alphabet variable names are drawn from. -/
  N : Type
  [nameAlphabet : NameAlphabet N]
  /-- Terms. -/
  Tm : Type
  /-- Types. -/
  Ty : Type

  /-- The typing judgement, over contexts keyed by `N`. -/
  HasType : Context N Ty → Tm → Ty → Prop

  /-- Single-step reduction. -/
  Step : Tm → Tm → Prop

  /-- Subject reduction. A field, not an assumption: building a `TypeSystem` proves it. -/
  Preservation : ∀ {Γ t τ t'}, HasType Γ t τ → Step t t' → HasType Γ t' τ

attribute [instance] TypeSystem.nameAlphabet

end LambdaLab.TypedLanguage
