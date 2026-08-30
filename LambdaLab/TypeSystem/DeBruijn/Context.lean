import LambdaLab.Nominal.Unification.Subst

/-!
# Typing contexts, indexed by position

The de Bruijn counterpart of `TypeSystem/Named/Context.lean`. A context there maps variable
*names* to types; here a variable *is* its distance to its binder, so a context is the list of
types in scope, most recent binder first, and lookup is positional.

Three things the named file works for are free here, and the differences are the point:

* **No key type, so no `Atom`.** The named context needs `Atom N` for `Std.HashMap`'s hashing;
  a list needs nothing, and the whole parameter disappears from the tower above.
* **Substitution is inherited, not declared.** The named file carries `instHasSubstContext` and a
  guard against the key-aware `HashMap` instance, because a context's keys must not count toward
  support. A list has no keys: the existing `HasSubst A (List α) β` (support = some element's,
  `pSubst` = `map`) says exactly the right thing, and the instance-selection saga does not exist.
* **Extensionality is available.** Two hashmaps agreeing at every key cannot be proved equal, so
  the named side states everything keywise and demands `cong` of every judgement. Lists agreeing
  at every index are equal (`List.ext_getElem?`), so here `pSubst` of a ground context *is* the
  context (`Context.pSubst_of_ground`, an equation), and `cong` is a theorem rather than a field
  (`LawfulTypeSystem.cong` in `Basic.lean`).

The operation is `Γ[i]?` — `getElem?`, the list's own — as the named side uses the hashmap's
`get?`; `Context.cons` takes no name, and extending under a binder is bare `cons` because the
*positions* shift rather than any stored data.
-/

namespace LambdaLab.TypeSystem.DeBruijn

variable {Ty : Type}

/-- A typing context: the types in scope, most recent binder first. -/
abbrev Context (Ty : Type) : Type := List Ty

/-- The empty context. -/
def Context.empty : Context Ty := []

/-- Extend a context under one more binder: the new type is index `0`, every existing index
shifts up — which is `cons`, with nothing to renumber, because positions moved rather than
data. -/
def Context.cons (τ : Ty) (Γ : Context Ty) : Context Ty := τ :: Γ

@[simp] theorem Context.getElem?_empty (i : Nat) :
    (Context.empty (Ty := Ty))[i]? = none := rfl

@[simp] theorem Context.getElem?_cons_zero (Γ : Context Ty) (τ : Ty) :
    (Γ.cons τ)[0]? = some τ := rfl

@[simp] theorem Context.getElem?_cons_succ (Γ : Context Ty) (τ : Ty) (i : Nat) :
    (Γ.cons τ)[i + 1]? = Γ[i]? := rfl

/-! ## Reading a substituted context

`pSubst` on a list is `map`, so lookup commutes with it — and unlike the named side, this is a
convenience rather than the only handle: the context equations below are available too. -/

theorem Context.pSubst_getElem? {A Ty : Type} [LambdaLab.Nominal.Atom A]
    [HasSubst A Ty Ty] (Γ : Context Ty) (σ : Subst A Ty) (i : Nat) :
    (HasSubst.pSubst Γ σ)[i]? = Γ[i]?.map (fun τ => HasSubst.pSubst τ σ) := by
  show (Γ.map (fun τ => HasSubst.pSubst τ σ))[i]? = _
  rw [List.getElem?_map]

/-- **A ground context is unchanged by substitution** — as an equation on contexts, which the
named side cannot state (no hashmap extensionality) and this side gets from `map`. -/
theorem Context.pSubst_of_ground {A Ty : Type} [LambdaLab.Nominal.Atom A]
    [HasSubst A Ty Ty] [GroundStable A Ty Ty] (Γ : Context Ty) (σ : Subst A Ty)
    (hΓ : ∀ τ ∈ Γ, HasVars.Ground (A := A) τ) :
    HasSubst.pSubst Γ σ = Γ := by
  show Γ.map (fun τ => HasSubst.pSubst τ σ) = Γ
  calc Γ.map (fun τ => HasSubst.pSubst τ σ)
      = Γ.map id := List.map_congr_left fun τ hτ => GroundStable.pSubst_ground σ (hΓ τ hτ)
    _ = Γ := List.map_id _

end LambdaLab.TypeSystem.DeBruijn
