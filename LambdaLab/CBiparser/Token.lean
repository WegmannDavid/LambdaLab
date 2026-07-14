/-!
# Tokens

The alphabet shared by the tokenizer and every token-level biparser. Extracted out of
`Mixfix/Basic.lean` so that `Tokenizer.lean` does not have to depend on the mixfix stack — a
tokenizer knows nothing about grammars.

A **token** is a string that is *non-empty* and contains *no separator character*. Both halves are
load-bearing, and both are in the type rather than beside it:

* **separator-free** — a token containing a separator would re-lex as *two* tokens, so rendering
  and re-tokenizing would not be the identity;
* **non-empty** — an empty token would render to nothing and vanish, so two different token lists
  could render alike.

Together they are exactly what makes `tokenize (render ts) = ts` provable.
-/

namespace LambdaLab.CBiparser

/-- A predicate-restricted string. -/
abbrev Restricted (P : String → Prop) : Type := { s : String // P s }

/-- A **token** for the separator predicate `sep`: a **nonempty** string containing **no**
separator character. -/
abbrev Token (sep : Char → Bool) : Type :=
  Restricted (fun s => (∀ c ∈ s.toList, sep c = false) ∧ s.toList ≠ [])

/-- A token's characters are never empty. -/
theorem Token.toList_ne_nil {sep : Char → Bool} (t : Token sep) : t.val.toList ≠ [] := t.2.2

/-- A token contains no separator. -/
theorem Token.no_sep {sep : Char → Bool} (t : Token sep) :
    ∀ c ∈ t.val.toList, sep c = false := t.2.1

/-- Tokens are equal exactly when their characters are. -/
theorem Token.eq_of_toList {sep : Char → Bool} {t u : Token sep}
    (h : t.val.toList = u.val.toList) : t = u := by
  apply Subtype.ext
  apply String.ext
  exact h

end LambdaLab.CBiparser
