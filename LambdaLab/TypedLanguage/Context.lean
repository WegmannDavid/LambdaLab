import LambdaLab.TypedLanguage.NameAlphabet

/-!
# Typing contexts, parametric in the name alphabet

A context maps variable names to types. Copied here from `Pipeline/Basic.lean` — the reference
interface, whose `Context Ty` is hard-wired to `Std.HashMap String Ty` — and generalized: the key
type is now any `NameAlphabet N`.

That generality is the point. A parsed term is named by the *tokens* the grammar admits
(`Term VName`), not by arbitrary strings, so the context it is typed under has to be keyed by the
same `N`. A `String`-keyed context cannot receive one without a conversion at the boundary, which
is exactly the impedance mismatch the name parameter exists to remove.

This is also the first place the `Hashable` field of `NameAlphabet` earns its keep: it is required
by `Std.HashMap`, and by nothing else in the interface. If contexts ever stop being hashmaps, that
field can go.

The lemmas are the two from `Stlc/Named/Typing/Basic.lean`'s `Ctx`, generalized unchanged —
`decEq` supplies the `LawfulBEq` that `getElem?_insert` needs.
-/

namespace LambdaLab.Language

variable {N : Type} [NameAlphabet N] {Ty : Type}

/-- A typing context: a hashmap from variable names to types. -/
abbrev Context (N : Type) [NameAlphabet N] (Ty : Type) : Type := Std.HashMap N Ty

/-- The empty context. -/
def Context.empty : Context N Ty := ∅

/-- Extend a context with a binding `x : τ`. The new binding shadows any previous binding of
`x`. -/
def Context.cons (x : N) (τ : Ty) (Γ : Context N Ty) : Context N Ty :=
  Γ.insert x τ

@[simp] theorem Context.get?_empty (x : N) :
    (Context.empty (N := N) (Ty := Ty)).get? x = none := by
  simp [Context.empty]

@[simp] theorem Context.get?_cons (Γ : Context N Ty) (x : N) (τ : Ty) (y : N) :
    (Γ.cons x τ).get? y = if x = y then some τ else Γ.get? y := by
  rw [Context.cons, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hbeq : (x == y) = false := by simp [hxy]
    rw [hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, hxy]
    rw [← Std.HashMap.get?_eq_getElem?]

end LambdaLab.Language
