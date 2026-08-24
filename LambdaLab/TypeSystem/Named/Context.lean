import LambdaLab.Nominal.Atom
import LambdaLab.Nominal.Unification.Subst

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

**Why not the generic `HashMap` instance.** `Nominal/Unification/Subst.lean` already has
`HasSubst A (Std.HashMap K V) β`, and `Context N Ty` is by definition a `Std.HashMap N Ty`, so
that instance would do — except it also asks for `HasVars A K`, because it lets *keys* contribute
to support. That is right for `Subst A 𝕊 = HashMap A 𝕊`, where the keys *are* the atoms being
substituted. It is wrong here: the keys of a typing context are binder names, which are never
metavariables.

So this instance drops the key clause: support is "occurs in some value".

**It overlaps the generic instance, so it is declared `low`.** `Context N Ty` *is*
`Std.HashMap N Ty`, and the two are not interchangeable: the generic `isFree` is
`isFree key a ∨ isFree val a`, this one is `isFree val a`, and `False ∨ P` is not *definitionally*
`P`. A lemma proved about one will not fire against the other. At default priority that broke the
build once, instructively: the same lemma at the same type got different instances in different
files, decided by import set.

**What the atom parameter fixed.** Before the port the two instances were separated by whether
the *key type* had a `HasVars` — which made them hostage to which types happened to have one, and
`Atom Nat` nearly upset it. Now they are separated by which *atom type* is being substituted. A
substitution binds atoms of `A` and is keyed by `A`, so `HasVars A A` applies and the key-aware
instance wins. A context is keyed by names of an unrelated `N`, there is no `HasVars A N`, and
only this instance can fire. The `low` priority is belt to that braces, and the guards below pin
both directions rather than assuming them. -/

/-- Substitution into a context: map over the values, leave the keys alone. -/
instance (priority := low) instHasSubstContext {A N Ty β : Type}
    [LambdaLab.Nominal.Atom A] [Atom N] [HasSubst A Ty β] :
    HasSubst A (Context N Ty) β where
  isFree Γ a := ∃ p ∈ Γ.toList, HasVars.isFree p.2 a
  supp Γ := Γ.toList.flatMap (fun p => HasVars.supp (A := A) p.2)
  mem_supp_iff_isFree Γ a := by
    simp only [List.mem_flatMap, HasVars.mem_supp_iff_isFree]
  pSubst Γ σ := Γ.map (fun _ v => HasSubst.pSubst v σ)

/-! ### Which instance fires where — guarded, not assumed

Both directions are pinned below by `rfl` on the instance itself. They cost nothing and they fail
loudly the day the balance shifts. They were once written anticipating "the day someone gives
`Nat` an `Atom` instance"; that day came, and they held. Do not delete them. -/

/-- Substitutions keep the key-aware instance: a substitution's keys *are* the atoms it binds, so
they must count towards support. -/
example {A S : Type} [LambdaLab.Nominal.Atom A] [HasSubst A S S] :
    (inferInstance : HasSubst A (Subst A S) S) = instHasSubstHashMap := rfl

/-- Contexts get the value-only instance: their keys are binder names, never metavariables. -/
example {A N Ty : Type} [LambdaLab.Nominal.Atom A] [Atom N] [HasSubst A Ty Ty] :
    (inferInstance : HasSubst A (Context N Ty) Ty) = instHasSubstContext := rfl

/-! ## Reading a substituted context

Substitution maps over the values, so lookup commutes with it. This is the *only* handle anything
gets on a substituted context: `Std.HashMap` has no `getElem?` extensionality here, so two contexts
that agree at every key cannot be proved equal — a client must reason through `get?` and a typing
judgement that respects it (`TypeSystem.Named.LawfulTypeSystem.cong`). -/

theorem Context.pSubst_get? {A N Ty : Type} [LambdaLab.Nominal.Atom A] [Atom N]
    [HasSubst A Ty Ty] (Γ : Context N Ty) (σ : Subst A Ty) (x : N) :
    (HasSubst.pSubst Γ σ).get? x = (Γ.get? x).map (fun τ => HasSubst.pSubst τ σ) := by
  show (Γ.map (fun _ v => HasSubst.pSubst v σ)).get? x = _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map,
      ← Std.HashMap.get?_eq_getElem?]

/-- **A ground context is unchanged by substitution**, keywise. The equation on contexts is not
available (no extensionality), which is why this is stated at `get?`. -/
theorem Context.pSubst_get?_of_ground {A N Ty : Type} [LambdaLab.Nominal.Atom A] [Atom N]
    [HasSubst A Ty Ty] [GroundStable A Ty Ty] (Γ : Context N Ty) (σ : Subst A Ty)
    (hΓ : ∀ (x : N) (τ : Ty), Γ.get? x = some τ → HasVars.Ground (A := A) τ) (x : N) :
    (HasSubst.pSubst Γ σ).get? x = Γ.get? x := by
  rw [Context.pSubst_get?]
  cases hx : Γ.get? x with
  | none => rfl
  | some τ => exact congrArg some (GroundStable.pSubst_ground σ (hΓ x τ hx))

end LambdaLab.TypeSystem.Named
