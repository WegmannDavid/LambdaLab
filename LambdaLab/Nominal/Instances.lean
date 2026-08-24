import LambdaLab.Nominal.Atom

/-!
# Atom instances

`Nominal/Atom.lean` states what a supply of names must provide; this file supplies one. Keeping
the two apart means the class can sit at the bottom of every named development without also
fixing *which* type the names are: a module that only needs `[Atom N]` imports `Atom.lean` and
gets no instance, and a module that wants to run at `String` imports this and gets one.

## `String` is a supply of atoms

The generator returns a string strictly longer than every string in `used`, hence absent from it.
Length is the whole argument — no reasoning about spellings — which is why the same trick
reappears verbatim for `FreeName` in `TypeSystem/Named/FreeName.lean`, the repo's other `Atom`
instance. That one cannot live here: its atoms are carved out of a grammar's reserved `Token`s,
so it depends on `Pipeline/`, and `Nominal/` must never import back into `Pipeline/`. `String`
has no such dependency, so it does live here, and `le_foldr_max` — the list lemma both proofs
turn on — comes with it.

## `Nat` is a supply of atoms

The same argument with the length step deleted: `used.foldr max 0 + 1` is bigger than everything
in `used`, so it is not in `used`, and `le_foldr_max` proves it directly rather than through a
`String.length`. It is here for the nominal development rather than for the object languages —
`Perm`, support and α-equivalence want a concrete atom type to test against, and one whose
freshness is arithmetic keeps `decide` and `omega` usable in those proofs. Nothing in `Stlc/`
uses it.

Like `Atom.lean`, and unlike the rest of `Nominal/`, this file must stay Mathlib-free: the `stlc`
and `arith` executables run at `String`, so their import cone runs through here.
-/

namespace LambdaLab.Nominal

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

/-! ## `Nat` is a supply of atoms -/

/-- One more than every element of `used`. -/
def natFreshFor (used : List Nat) : Nat := used.foldr max 0 + 1

theorem natFreshFor_not_in (used : List Nat) : natFreshFor used ∉ used := by
  intro h_in
  have h_le : natFreshFor used ≤ used.foldr max 0 := le_foldr_max _ _ h_in
  simp only [natFreshFor] at h_le
  omega

instance : Atom Nat where
  decEq := inferInstance
  freshFor := natFreshFor
  freshFor_not_in := natFreshFor_not_in

end LambdaLab.Nominal
