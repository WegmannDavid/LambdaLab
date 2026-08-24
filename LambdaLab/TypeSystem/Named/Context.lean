import LambdaLab.Nominal.Atom
import LambdaLab.Substitution.Basic

/-!
# Typing contexts, parametric in the atoms

A context maps variable names to types. Copied here from `Pipeline/Basic.lean` — the reference
interface, whose `Context Ty` is hard-wired to `Std.HashMap String Ty` — and generalized: the key
type is now any `Atom N`.

That generality is the point. A parsed term is named by the *tokens* the grammar admits
(`Term VName`), not by arbitrary strings, so the context it is typed under has to be keyed by the
same `N`. A `String`-keyed context cannot receive one without a conversion at the boundary, which
is exactly the impedance mismatch the name parameter exists to remove.

This is also the first place the `Hashable` field of `Atom` earns its keep: it is required
by `Std.HashMap`, and by nothing else in the interface. If contexts ever stop being hashmaps, that
field can go.

The lemmas are the two from `Stlc/Named/Typing/Basic.lean`'s `Ctx`, generalized unchanged —
`decEq` supplies the `LawfulBEq` that `getElem?_insert` needs.
-/

namespace LambdaLab.TypeSystem.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N] {Ty : Type}

/-- A typing context: a hashmap from variable names to types. -/
abbrev Context (N : Type) [Atom N] (Ty : Type) : Type := Std.HashMap N Ty

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

/-! ## Substitution into a context

A context is substitutable as soon as its *values* are: `pSubst` maps over the values and leaves
the keys alone.

**Why not the generic `HashMap` instance.** `Substitution/Basic.lean` already has
`HasSubst (Std.HashMap K V) β`, and `Context N Ty` is by definition a `Std.HashMap N Ty`, so that
instance would do — except it also asks for `HasVars K`, because it lets *keys* contribute to
support. That is right for `Subst 𝕊 = HashMap Nat 𝕊`, where the keys are the metavariables. It is
wrong here: the keys of a typing context are binder names, which are never metavariables. Paying
for it means every consumer carries a `[HasVars N]` it has no use for — which is exactly what the
whole `Stlc/Named/Typing` stack does today, on nine `variable` lines.

So this instance drops the key clause: support is "free in some value", and `fresh` is a max-fold
over values only.

**It overlaps the generic instance, so it is declared `low`.** `Context N Ty` *is*
`Std.HashMap N Ty`, so both instances apply whenever the key type has an `Atom` instance, and they
are not interchangeable: the generic `isFree` is `isFree key n ∨ isFree val n`, this one is
`isFree val n`, and `False ∨ P` is not *definitionally* `P`. A lemma proved about one will not
fire against the other.

At default priority that broke the build, and instructively. `Unification.lean` does not import
this file, so `HashMap.pSubst_get?` was stated against the generic instance; `Properties.lean`
does import it, so its goals got this one, and the `rw` no longer matched. Same lemma, same type,
two instances — decided by import set.

`low` makes this the *fallback*: wherever `[HasVars N]` is available the generic instance wins, so
every existing proof keeps the instance it was written against. This one fires only where the
generic cannot apply — which is the whole point, since not needing `[HasVars N]` is what it is
for.

`Subst 𝕊 = Std.HashMap Nat 𝕊` is untouched either way, and it matters that it is:
substitution-into-substitution must keep the key-aware support semantics that unification depends
on.

⚠ **The reason it is untouched changed on 2026-08-24.** It used to be that `Nat` had no `Atom`
instance, so this instance could not even apply to a `Subst`. `Nominal/Instances.lean` now gives
`Nat` one, so both instances apply and the *only* thing keeping the key-aware one is `low` here
plus `HasVars Nat` being available at default priority. The guards below stopped being a formality
and started being the proof. The remaining hazard is the mirror image of the old one: **delete or
demote `HasVars Nat` and every substitution silently acquires value-only support.** -/

/-- Substitution into a context: map over the values, leave the keys alone. -/
instance (priority := low) {N Ty β : Type} [Atom N] [HasSubst Ty β] :
    HasSubst (Context N Ty) β where
  pSubst Γ σ := Γ.map (fun _ v => HasSubst.pSubst v σ)
  isFree Γ n := ∃ p ∈ Γ.toList, HasVars.isFree p.2 n
  fresh Γ := Γ.toList.foldr (fun p acc => max acc (HasVars.fresh p.2)) 0
  fresh_gt_free := by
    intro Γ n h
    obtain ⟨p, hp, hf⟩ := h
    have key := List.foldr_max_of_mem (fun q : N × Ty => HasVars.fresh q.2) Γ.toList p hp
    exact Nat.lt_of_lt_of_le (HasVars.fresh_gt_free _ _ hf) key

/-! ### Which instance fires where — guarded, not assumed

Two instances now apply to `Std.HashMap`, so *which* one elaborates is a real property of the
environment rather than a local fact. Both directions are pinned below, by `rfl` on the instance
itself. They cost nothing and they fail loudly the day the balance shifts.

They were written anticipating "the day someone gives `Nat` an `Atom` instance". That day came
(`835e83c`) and they held, because `low` had already covered it — but they are now the load-bearing
check rather than a precaution, so do not delete them. -/

/-- Substitutions keep the key-aware instance: for `Subst 𝕊 = HashMap Nat 𝕊` the keys *are* the
metavariables, so they must count towards support. -/
example {S : Type} [HasSubst S S] :
    (inferInstance : HasSubst (Subst S) S) = instHasSubstHashMapOfHasVars := rfl

/-- Contexts get the value-only instance: their keys are binder names, never metavariables. -/
example {N Ty : Type} [Atom N] [HasSubst Ty Ty] :
    (inferInstance : HasSubst (Context N Ty) Ty) = instHasSubstContext := rfl

/-! ## Reading a substituted context

Substitution maps over the values, so lookup commutes with it. This is the *only* handle anything
gets on a substituted context: `Std.HashMap` has no `getElem?` extensionality here, so two contexts
that agree at every key cannot be proved equal — a client must reason through `get?` and a typing
judgement that respects it (`TypeSystem.Named.LawfulTypeSystem.cong`). -/

theorem Context.pSubst_get? {N Ty : Type} [Atom N] [HasSubst Ty Ty]
    (Γ : Context N Ty) (σ : Subst Ty) (x : N) :
    (HasSubst.pSubst Γ σ).get? x = (Γ.get? x).map (fun τ => HasSubst.pSubst τ σ) := by
  show (Γ.map (fun _ v => HasSubst.pSubst v σ)).get? x = _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map,
      ← Std.HashMap.get?_eq_getElem?]

/-- **A ground context is unchanged by substitution**, keywise. The equation on contexts is not
available (no extensionality), which is why this is stated at `get?`. -/
theorem Context.pSubst_get?_of_ground {N Ty : Type} [Atom N] [HasSubst Ty Ty]
    [GroundStable Ty Ty] (Γ : Context N Ty) (σ : Subst Ty)
    (hΓ : ∀ (x : N) (τ : Ty), Γ.get? x = some τ → HasVars.Ground τ) (x : N) :
    (HasSubst.pSubst Γ σ).get? x = Γ.get? x := by
  rw [Context.pSubst_get?]
  cases hx : Γ.get? x with
  | none => rfl
  | some τ => exact congrArg some (GroundStable.pSubst_ground σ (hΓ x τ hx))

end LambdaLab.TypeSystem.Named
