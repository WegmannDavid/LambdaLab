import Std.Data.HashMap

/-!
# `NameAlphabet` — what an object language needs of a variable name

A named object language should be parametric in its type of variable names. Everything a
named presentation does — renaming, capture-avoiding substitution, typing, reduction,
confluence, normalization — treats a name as opaque; the *only* operations performed are
deciding equality, keying a context, and generating a name not already in use. That is the
whole interface:

* `DecidableEq` — substitution and typing compare names;
* `Hashable` — contexts are `Std.HashMap`s keyed by names (`TypeSystem.Context`, which
  `Stlc.Named.Ctx` now *is*);
* `freshFor` + `freshFor_not_in` — capture-avoiding substitution must rename a binder out of the
  way, so it needs a name outside any given finite set.

Being parametric is what lets the *parser* hand the development a name type whose values are
already known to be well-formed surface tokens (`Stlc.Named.VName`), instead of `String`, which admits
`""` and keywords and so cannot round-trip. The alternative — a subtype `{t : Term // …}` — would
put proofs inside the data and force `Subtype.ext` into every lemma; a parameter costs nothing at
use sites.

It lives in `TypeSystem/` because it is what a *typed* object language needs of a name, below
and independent of any concrete syntax: it imports nothing but `Std.HashMap`, and `Pipeline/`
depends on it rather than the other way round.

The module is `NameAlphabet`, not `Name`: `Pipeline.Name` is already the vernacular's
declaration-name type.

## Status: in use

`Stlc.Named.Term`, `Ctx`, `HasType` and `infer` are all parametric in `N`, and `Stlc.Named.Ctx N`
is *definitionally* `TypeSystem.Context N Ty` — which is what lets a parsed term, named by the
tokens the grammar admits, be typed with no conversion at the interface boundary. The design fact
this file set out to establish held up: **the interface is this small.** Across `Stlc/Named`,
`String`-specific code was confined to one 30-line block (the fresh-name generator and its proof,
below), used at three call sites; everything downstream is simply pinned at `String`.
-/

namespace LambdaLab.TypeSystem

/-- A type usable as variable names: decidable equality, hashable, and an inexhaustible supply. -/
class NameAlphabet (N : Type) extends Hashable N where
  decEq : DecidableEq N
  /-- A name outside `used`. -/
  freshFor : List N → N
  freshFor_not_in : ∀ used : List N, freshFor used ∉ used

attribute [instance] NameAlphabet.decEq

export NameAlphabet (freshFor freshFor_not_in)

/-! ## `String` is a name alphabet

The generator returns a string strictly longer than every string in `used`, hence absent from it.
-/

def stringFreshFor (used : List String) : String :=
  String.ofList (List.replicate ((used.map String.length).foldr max 0 + 1) 'a')

/-- Every element of `l` is bounded above by `l.foldr max 0`. -/
theorem le_foldr_max : ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro a hl; cases hl
  | cons x xs ih =>
      intro a hl
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hl with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih a h) (Nat.le_max_right _ _)

theorem stringFreshFor_not_in (used : List String) : stringFreshFor used ∉ used := by
  intro h_in
  have h_len_in : (stringFreshFor used).length ∈ used.map String.length :=
    List.mem_map.mpr ⟨stringFreshFor used, h_in, rfl⟩
  have h_le : (stringFreshFor used).length ≤ (used.map String.length).foldr max 0 :=
    le_foldr_max _ _ h_len_in
  have h_eq : (stringFreshFor used).length = (used.map String.length).foldr max 0 + 1 := by
    show (String.ofList
        (List.replicate ((used.map String.length).foldr max 0 + 1) 'a')).length = _
    rw [String.length_ofList]
    exact List.length_replicate
  omega

instance : NameAlphabet String where
  decEq := inferInstance
  freshFor := stringFreshFor
  freshFor_not_in := stringFreshFor_not_in

end LambdaLab.TypeSystem
