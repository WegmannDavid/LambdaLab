import Std.Data.HashMap

/-!
# `NameAlphabet` — what the named development needs of a variable name

`Stlc/Named` is parametric in the type of variable names. Everything in it — renaming,
capture-avoiding substitution, typing, reduction, confluence, normalization — treats a name as
opaque; the *only* operations it performs are deciding equality, keying a context, and
generating a name not already in use. That is the whole interface:

* `DecidableEq` — substitution and typing compare names;
* `Hashable` — the context is a `Std.HashMap` keyed by names;
* `freshFor` + `freshFor_not_in` — capture-avoiding substitution must rename a binder out of the
  way, so it needs a name outside any given finite set.

Being parametric is what lets the *parser* hand the development a name type whose values are
already known to be well-formed surface tokens (`Lang1.VName`), instead of `String`, which admits
`""` and keywords and so cannot round-trip. The alternative — a subtype `{t : Term // …}` — would
put proofs inside the data and force `Subtype.ext` into every lemma; a parameter costs nothing at
use sites.

## Status: this class is the *first step* of that parameterization, and is not yet used

`Term` is still `String`-named. The remaining work is to thread `{N} [NameAlphabet N]` through
`Stlc/Named`; an attempt at it is recorded in the notes. What this file already establishes is the
main design fact: **the interface is this small.** Renaming, substitution, typing, reduction,
confluence and normalization touch a name only through decidable equality, hashing, and fresh-name
generation — nothing else. Delete this file if the parameterization is abandoned.
-/

namespace LambdaLab.Stlc.Named

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

end LambdaLab.Stlc.Named
