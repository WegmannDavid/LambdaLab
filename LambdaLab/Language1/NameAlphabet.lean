import Std.Data.HashMap

/-!
# `NameAlphabet` — what an object language needs of a variable name

A named object language should be parametric in its type of variable names. Everything a
named presentation does — renaming, capture-avoiding substitution, typing, reduction,
confluence, normalization — treats a name as opaque; the *only* operations performed are
deciding equality, keying a context, and generating a name not already in use. That is the
whole interface:

* `DecidableEq` — substitution and typing compare names;
* `Hashable` — contexts are `Std.HashMap`s keyed by names (`Stlc.Named.Ctx`, and the legacy
  `Language.Context`);
* `freshFor` + `freshFor_not_in` — capture-avoiding substitution must rename a binder out of the
  way, so it needs a name outside any given finite set.

Being parametric is what lets the *parser* hand the development a name type whose values are
already known to be well-formed surface tokens (`Lang1.VName`), instead of `String`, which admits
`""` and keywords and so cannot round-trip. The alternative — a subtype `{t : Term // …}` — would
put proofs inside the data and force `Subtype.ext` into every lemma; a parameter costs nothing at
use sites.

It lives in `Language1/` because that is the live language interface — the one that will absorb
the elaboration side (typing relation, elaborator, evaluator) currently sitting in `Language/`,
which is kept only as a reference. Nothing about the class is STLC-specific, and both context
types it is meant to serve (`Stlc.Named.Ctx` and `Language.Context`) are `Std.HashMap String Ty`
today.

The module is `NameAlphabet`, not `Name`: `Language1.Name` is already the vernacular's
declaration-name type.

## Status: this class is the *first step* of that parameterization, and is not yet used

`Stlc.Named.Term` is still `String`-named, as is `Language.Context`. The remaining work is to
thread `{N} [NameAlphabet N]` through the named development, and — when elaboration moves into
`Language1` — through the context type it brings with it. What this file already establishes is the main design
fact: **the interface is this small.** Across all 14 files of `Stlc/Named`, `String`-specific code
was confined to one 30-line block (the fresh-name generator and its proof, now below), used at
three call sites. Delete this file if the parameterization is abandoned.
-/

namespace LambdaLab.Language1

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

end LambdaLab.Language1
