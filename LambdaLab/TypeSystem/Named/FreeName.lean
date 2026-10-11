import LambdaLab.Pipeline.Basic
import LambdaLab.Nominal.Instances

/-!
# `FreeName` — the atoms a language gets from its reserved list

Every language in this vernacular fixes a finite list of *reserved* tokens: its grammar's name
parts plus the vernacular keywords. Whatever is left over is exactly what may be used as a
variable name. That leftover type has an `Atom` instance, and the proof is the same for every
language — so it is discharged once, here, rather than per language.

```lean
abbrev VName := FreeName sReserved      -- and the instance comes for free
```

The fresh-name generator is the classic trick: a run of the lexicon's `fresh` character (a word
character, so the run is one token) longer than every token in
`used ++ reserved`. Length alone then settles both obligations — the result is absent from `used`
(what `freshFor_not_in` asks) *and* absent from `reserved` (what makes it a `FreeName` at all).
Working with lengths avoids having to reason about the reserved tokens' spellings.

## A note on where this file sits

It is filed under `TypeSystem/` with `Context`, because an `Atom` instance is what it produces.
It is no longer filed with the *class* it instantiates: `Atom` moved down to `Nominal/Atom.lean`.
And unlike `Context` it depends *upwards*, on `Pipeline/Basic.lean`: the atoms it builds are
carved out of the grammar's reserved `Token`s, and `Token` is concrete syntax. So this is the one
module whose folder does not match its layer. Moving it to `Pipeline/` would restore the layering,
and now that the class has moved away, nothing argues against it but the churn.
-/

namespace LambdaLab.TypeSystem.Named

open LambdaLab.Parser.IsoParser LambdaLab.Pipeline
open LambdaLab.Nominal (Atom freshFor freshFor_not_in le_foldr_max)

-- `isFree` and `FreeName` are declared in `Pipeline/Basic.lean`, so that `Pipeline.Name` and a
-- language's own name type can be phrased with them; this file adds the instance.

/-! ## A supply of arbitrarily long tokens -/

/-- `n+1` repetitions of the lexicon's fresh character — a non-empty run of word characters, so
a genuine `Token`. -/
private def aRun (lex : Lexicon) (n : Nat) : Token lex :=
  Token.ofWord (List.replicate (n + 1) lex.fresh)
    (fun c hc => by rw [(List.mem_replicate.mp hc).2]; exact lex.fresh_word) (by simp)

private theorem aRun_length (lex : Lexicon) (n : Nat) : (aRun lex n).val.length = n + 1 := by
  show (String.ofList (List.replicate (n + 1) lex.fresh)).length = n + 1
  rw [String.length_ofList]
  exact List.length_replicate

variable {lex : Lexicon}

/-- The longest token in a list. -/
private def maxLen (l : List (Token lex)) : Nat := (l.map (fun t => t.val.length)).foldr max 0

private theorem le_maxLen {l : List (Token lex)} {t : Token lex} (h : t ∈ l) :
    t.val.length ≤ maxLen l :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨t, h, rfl⟩)

/-- A run longer than everything in `l` is not in `l`. -/
private theorem aRun_maxLen_not_mem {l : List (Token lex)} : aRun lex (maxLen l) ∉ l := by
  intro h
  have hle := le_maxLen h
  rw [aRun_length] at hle
  omega

/-! ## The instance -/

instance instAtomFreeName (reserved : List (Token lex)) : Atom (FreeName reserved) where
  hash v := hash v.val.val
  decEq := inferInstance
  freshFor used :=
    ⟨aRun lex (maxLen (used.map (fun v => v.val) ++ reserved)), by
      simp only [isFree, decide_eq_true_eq]
      exact fun hmem => aRun_maxLen_not_mem (List.mem_append_right _ hmem)⟩
  freshFor_not_in used := by
    intro hmem
    have hval : aRun lex (maxLen (used.map (fun v => v.val) ++ reserved))
        ∈ used.map (fun v => v.val) :=
      List.mem_map.mpr ⟨_, hmem, rfl⟩
    exact aRun_maxLen_not_mem (List.mem_append_left _ hval)

end LambdaLab.TypeSystem.Named
