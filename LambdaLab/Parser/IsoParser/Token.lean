/-!
# Tokens

The alphabet shared by the tokenizer and every token-level biparser. It lives here, above both, so
that the tokenizer need not depend on the mixfix stack — a tokenizer knows nothing about
grammars — and so that a *client* (`Language1`) can derive its own token type by instantiating
`sep` rather than rolling its own.

A **token** is a string that is *non-empty* and contains *no separator character*. Both halves are
load-bearing, and both sit in the type rather than beside it:

* **separator-free** — a token containing a separator would re-lex as *two* tokens, so rendering
  and re-tokenizing would not be the identity;
* **non-empty** — an empty token would render to nothing and vanish, so two different token lists
  could render alike.

Together they are exactly what makes `tokens (render ts) = ts` provable — and, unexpectedly,
non-emptiness is also what discharges the *progress* obligation of the char-level composite: one
token consumed costs at least one character.

## Why the predicate is a `Bool`

`isToken` is a **decidable Bool**, not a `Prop` conjunction. That is what lets a client write a
token literal as `⟨"def", by decide⟩` — and it is why `Language1` can simply set
`abbrev Token := IsoParser.Token isSep` instead of defining a parallel type of its own.
-/

namespace LambdaLab.Parser.IsoParser

/-- A predicate-restricted string. -/
abbrev Restricted (P : String → Bool) : Type := { s : String // P s = true }

/-- Is `s` a well-formed token for the separator predicate `sep`: **non-empty** and containing
**no** separator? Decidable, so token literals are discharged by `decide`. -/
def isToken (sep : Char → Bool) (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => !sep c)

/-- **The token alphabet**, parameterised by which characters separate tokens. -/
abbrev Token (sep : Char → Bool) : Type := Restricted (isToken sep)

instance {sep : Char → Bool} : DecidableEq (Token sep) := Subtype.instDecidableEq

/-! ## Unpacking the invariant

`isToken` is stated as a `Bool` for `decide`'s sake; these give it back in the form proofs want. -/

/-- A string is empty exactly when its characters are. -/
theorem toList_eq_nil_iff {s : String} : s.toList = [] ↔ s = "" :=
  ⟨fun h => String.ext (by rw [h]; rfl), fun h => by rw [h]; rfl⟩

/-- `!isEmpty` is exactly "the characters are non-empty". -/
theorem isEmpty_eq_false_iff {s : String} : s.isEmpty = false ↔ s.toList ≠ [] := by
  constructor
  · intro h hn
    rw [toList_eq_nil_iff.mp hn] at h
    exact absurd h (by decide)
  · intro h
    cases he : s.isEmpty with
    | false => rfl
    | true => exact absurd (toList_eq_nil_iff.mpr (String.isEmpty_iff.mp he)) h

theorem isToken_iff {sep : Char → Bool} {s : String} :
    isToken sep s = true ↔ (∀ c ∈ s.toList, sep c = false) ∧ s.toList ≠ [] := by
  simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    isEmpty_eq_false_iff]
  constructor
  · rintro ⟨hne, hall⟩
    exact ⟨fun c hc => by simpa using hall c hc, hne⟩
  · rintro ⟨hall, hne⟩
    exact ⟨hne, fun c hc => by simp [hall c hc]⟩

/-- A token's characters are never empty. -/
theorem Token.toList_ne_nil {sep : Char → Bool} (t : Token sep) : t.val.toList ≠ [] :=
  (isToken_iff.mp t.2).2

/-- A token contains no separator. -/
theorem Token.no_sep {sep : Char → Bool} (t : Token sep) :
    ∀ c ∈ t.val.toList, sep c = false := (isToken_iff.mp t.2).1

/-- Tokens are equal exactly when their characters are. -/
theorem Token.eq_of_toList {sep : Char → Bool} {t u : Token sep}
    (h : t.val.toList = u.val.toList) : t = u := by
  apply Subtype.ext
  apply String.ext
  exact h

end LambdaLab.Parser.IsoParser
