import LambdaLab.Pipeline.Basic
import LambdaLab.TypedLanguage.NameAlphabet

/-!
# `FreeName` — the name alphabet a language gets from its reserved list

Every language in this vernacular fixes a finite list of *reserved* tokens: its grammar's name
parts plus the vernacular keywords. Whatever is left over is exactly what may be used as a
variable name. That leftover type is a `NameAlphabet`, and the proof is the same for every
language — so it is discharged once, here, rather than per language.

```lean
abbrev VName := FreeName sReserved      -- and the instance comes for free
```

The fresh-name generator is the classic trick: a run of `'a'`s longer than every token in
`used ++ reserved`. Length alone then settles both obligations — the result is absent from `used`
(what `freshFor_not_in` asks) *and* absent from `reserved` (what makes it a `FreeName` at all).
Working with lengths avoids having to reason about the reserved tokens' spellings.

## A note on where this file sits

It is filed under `TypedLanguage/` with `NameAlphabet` and `Context`, because a `NameAlphabet`
instance is what it produces. But unlike those two it depends *upwards*, on `Pipeline/Basic.lean`:
the alphabet it builds is carved out of the grammar's reserved `Token`s, and `Token` is concrete
syntax. So this is the one module whose folder does not match its layer. Moving it to `Pipeline/`
would restore the layering at the cost of separating it from the class it instantiates.
-/

namespace LambdaLab.Language

open LambdaLab.Parser.IsoParser

-- `isFree` and `FreeName` are declared in `Pipeline/Basic.lean`, so that `Name` and
-- `Language.isVarName` can be phrased with them; this file adds the instance.

/-! ## A supply of arbitrarily long tokens -/

/-- `n+1` repetitions of `'a'` — non-empty and separator-free, so a genuine `Token`. -/
private def aRun (n : Nat) : Token :=
  ⟨String.ofList (List.replicate (n + 1) 'a'), isToken_iff.mpr (by
    rw [String.toList_ofList]
    refine ⟨?_, by simp⟩
    intro c hc
    rw [(List.mem_replicate.mp hc).2]
    decide)⟩

private theorem aRun_length (n : Nat) : (aRun n).val.length = n + 1 := by
  show (String.ofList (List.replicate (n + 1) 'a')).length = n + 1
  rw [String.length_ofList]
  exact List.length_replicate

/-- The longest token in a list. -/
private def maxLen (l : List Token) : Nat := (l.map (fun t => t.val.length)).foldr max 0

private theorem le_maxLen {l : List Token} {t : Token} (h : t ∈ l) : t.val.length ≤ maxLen l :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨t, h, rfl⟩)

/-- A run longer than everything in `l` is not in `l`. -/
private theorem aRun_maxLen_not_mem {l : List Token} : aRun (maxLen l) ∉ l := by
  intro h
  have hle := le_maxLen h
  rw [aRun_length] at hle
  omega

/-! ## The instance -/

instance instNameAlphabetFreeName (reserved : List Token) : NameAlphabet (FreeName reserved) where
  hash v := hash v.val.val
  decEq := inferInstance
  freshFor used :=
    ⟨aRun (maxLen (used.map (fun v => v.val) ++ reserved)), by
      simp only [isFree, decide_eq_true_eq]
      exact fun hmem => aRun_maxLen_not_mem (List.mem_append_right _ hmem)⟩
  freshFor_not_in used := by
    intro hmem
    have hval : aRun (maxLen (used.map (fun v => v.val) ++ reserved))
        ∈ used.map (fun v => v.val) :=
      List.mem_map.mpr ⟨_, hmem, rfl⟩
    exact aRun_maxLen_not_mem (List.mem_append_left _ hval)

end LambdaLab.Language
