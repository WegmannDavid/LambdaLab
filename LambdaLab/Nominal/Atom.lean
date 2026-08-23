import Std.Data.HashMap

/-!
# `Atom` — what an object language needs of a variable name

A named object language should be parametric in its type of variable names. Everything a
named presentation does — renaming, capture-avoiding substitution, typing, reduction,
confluence, normalization — treats a name as opaque; the *only* operations performed are
deciding equality, keying a context, and generating a name not already in use. That is the
whole interface:

* `DecidableEq` — substitution and typing compare names;
* `Hashable` — contexts are `Std.HashMap`s keyed by names (`TypeSystem.Named.Context`, which
  `Stlc.Named.Ctx` now *is*);
* `freshFor` + `freshFor_not_in` — capture-avoiding substitution must rename a binder out of the
  way, so it needs a name outside any given finite set.

Being parametric is what lets the *parser* hand the development a name type whose values are
already known to be well-formed surface tokens (`Stlc.Named.VName`), instead of `String`, which admits
`""` and keywords and so cannot round-trip. The alternative — a subtype `{t : Term // …}` — would
put proofs inside the data and force `Subtype.ext` into every lemma; a parameter costs nothing at
use sites.

It lives in `Nominal/` because a supply of names is the bottom of the nominal development:
freshness, swapping and support are all built on the guarantee this class makes, that names do
not run out. Nothing here mentions permutations or sorts, so the STLC tower can — and does —
import it without importing any of that; it still imports nothing but `Std.HashMap`, and
`TypeSystem/` and `Pipeline/` depend on it rather than the other way round. **That direction is
now load-bearing: `Nominal/` is a foundation, not a leaf, and must never import back into them.**

The class is `Atom`, not `Name` and no longer `NameAlphabet`: `Pipeline.Name` is already the
vernacular's declaration-name type, and what this describes is a supply of atoms — the nominal
reading is the primary one now that the file sits here.

`Nominal/Atom.lean` holds this and nothing else, so `Nominal/Basic.lean` no longer exists: with
every line of it being about atoms, an import-only module in front would have said nothing. The
rest of the nominal development gets its own files beside this one — permutations, support, the
nominal-set class — and each may use Mathlib, which this file may not, since the executables'
import cone runs through here.

## Status: in use

`Stlc.Named.Term`, `Ctx`, `HasType` and `infer` are all parametric in `N`, and `Stlc.Named.Ctx N`
is *definitionally* `TypeSystem.Named.Context N Ty` — which is what lets a parsed term, named by the
tokens the grammar admits, be typed with no conversion at the interface boundary. The design fact
this file set out to establish held up: **the interface is this small.** Across `Stlc/Named`,
`String`-specific code is confined to one 30-line block — the fresh-name generator and its proof,
below.

Reduction, the de Bruijn translation and subject reduction were once *stated* at `String` even
though nothing in them needed it; generalising them to an arbitrary `N` changed signatures and no
proofs. That is the interface's real test, and it passed: `Stlc/Named/TypeSystem.lean`'s whole
class tower is now parametric, which is what lets the vernacular — whose names are `VName`, not
`String` — reach it. What remains at `String` is only what genuinely detours through de Bruijn
*binder lists*: confluence, normalization, `eval`.
-/

namespace LambdaLab.Nominal

/-- A type usable as variable names: decidable equality, hashable, and an inexhaustible supply. -/
class Atom (N : Type) extends Hashable N where
  decEq : DecidableEq N
  /-- A name outside `used`. -/
  freshFor : List N → N
  freshFor_not_in : ∀ used : List N, freshFor used ∉ used

/-! `reducible` is required of instance-valued projections, and harmless here: `decEq` is the
only `DecidableEq N` an `Atom` instance offers, so there is no canonical instance for it to
displace. -/
attribute [reducible, instance] Atom.decEq

export Atom (freshFor freshFor_not_in)

/-! ## `String` is a supply of atoms

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

instance : Atom String where
  decEq := inferInstance
  freshFor := stringFreshFor
  freshFor_not_in := stringFreshFor_not_in

end LambdaLab.Nominal
