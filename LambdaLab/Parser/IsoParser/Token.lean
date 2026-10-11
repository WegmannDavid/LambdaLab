/-!
# Tokens, and the lexicon that says what a token is

The alphabet shared by the tokenizer and every token-level biparser. It lives here, above both, so
that the tokenizer need not depend on the mixfix stack — a tokenizer knows nothing about grammars.

## The lexicon: each language's choice

What counts as a token is a language's decision, made once in a `Lexicon`:

* **separators** end a token and are otherwise skipped (whitespace, in every lexicon here);
* **self-delimiting** characters (`punct`) are a token on their own, whatever is next to them —
  with `(` and `)` self-delimiting, `f(x)` is four tokens and `( x )` is the same four;
* every other character is a **word** character, and a maximal run of them is one token.

Two more knobs say how the canonical printer spaces self-delimiting tokens: no space after an
**opener**, none before a **closer**, one space everywhere else. They change nothing about what is
read — only what is printed — and they may only name self-delimiting characters, because only
those may touch a neighbour without a space.

`Lexicon.make opens closes others` builds one from lists; `Lexicon.plain` has no self-delimiting
characters at all, so tokens are exactly the whitespace-separated words.

## What a token is

A **token** is either a single non-separator character, or a run of two or more *word*
characters. Each half of that is load-bearing:

* **no separators** — a token containing one would re-lex as two;
* **no self-delimiting character inside a longer token** — it would split off;
* **non-empty** — an empty token would render to nothing and vanish.

Together they are exactly what makes `tokens (render ts) = ts` provable.

## Why the predicate is a `Bool`

`isToken` is a **decidable Bool**, not a `Prop` conjunction. That is what lets a language write a
token literal as `⟨"def", by decide⟩`.
-/

namespace LambdaLab.Parser.IsoParser

/-- **A lexicon**: which characters separate tokens, which are tokens on their own, and how the
latter are spaced when printed. -/
structure Lexicon where
  /-- Characters that end a token and are otherwise skipped. -/
  sep : Char → Bool
  /-- Self-delimiting characters: each is a token on its own. -/
  punct : Char → Bool
  /-- Printed with no space after. -/
  opens : Char → Bool
  /-- Printed with no space before. -/
  closes : Char → Bool
  sep_punct : ∀ c, sep c = true → punct c = false
  opens_punct : ∀ c, opens c = true → punct c = true
  closes_punct : ∀ c, closes c = true → punct c = true
  /-- The canonical printer's separators are separators. -/
  space_sep : sep ' ' = true
  newline_sep : sep '\n' = true
  /-- A word character, from which fresh names can be built. -/
  fresh : Char
  fresh_sep : sep fresh = false
  fresh_punct : punct fresh = false

namespace Lexicon

/-- A character that may be part of a longer token. -/
def word (lex : Lexicon) (c : Char) : Bool := !lex.sep c && !lex.punct c

theorem word_sep {lex : Lexicon} {c : Char} (h : lex.word c = true) : lex.sep c = false := by
  simp only [word, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1

theorem word_punct {lex : Lexicon} {c : Char} (h : lex.word c = true) : lex.punct c = false := by
  simp only [word, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

theorem word_of {lex : Lexicon} {c : Char} (hs : lex.sep c = false) (hp : lex.punct c = false) :
    lex.word c = true := by
  simp [word, hs, hp]

/-- A non-separator that is not a word character is self-delimiting. -/
theorem punct_of_not_word {lex : Lexicon} {c : Char} (hs : lex.sep c = false)
    (hw : lex.word c = false) : lex.punct c = true := by
  simp only [word, hs, Bool.not_false, Bool.true_and, Bool.not_eq_false'] at hw
  exact hw

theorem fresh_word (lex : Lexicon) : lex.word lex.fresh = true :=
  word_of lex.fresh_sep lex.fresh_punct

/-- **A lexicon from lists**: whitespace separates; `opens`, `closes` and `others` are
self-delimiting, and the first two are spaced as openers and closers. -/
def make (opens closes others : List Char)
    (h : ∀ c ∈ opens ++ closes ++ others, c.isWhitespace = false ∧ c ≠ 'a' := by decide) :
    Lexicon where
  sep := Char.isWhitespace
  punct c := decide (c ∈ opens ++ closes ++ others)
  opens c := decide (c ∈ opens)
  closes c := decide (c ∈ closes)
  sep_punct c hc := by
    simp only [decide_eq_false_iff_not]
    intro hm
    have := (h c hm).1
    rw [hc] at this
    cases this
  opens_punct c hc := by
    simp only [decide_eq_true_eq, List.mem_append] at hc ⊢
    exact .inl (.inl hc)
  closes_punct c hc := by
    simp only [decide_eq_true_eq, List.mem_append] at hc ⊢
    exact .inl (.inr hc)
  space_sep := by decide
  newline_sep := by decide
  fresh := 'a'
  fresh_sep := by decide
  fresh_punct := by
    simp only [decide_eq_false_iff_not]
    intro hm
    exact (h 'a' hm).2 rfl

/-- **Whitespace and nothing else**: a token is a whitespace-separated word. -/
def plain : Lexicon := make [] [] []

/-- In a lexicon made from lists, a character in none of them that is not whitespace is a word
character. -/
theorem make_word {opens closes others : List Char} {h} {c : Char} (hw : c.isWhitespace = false)
    (hn : c ∉ opens ++ closes ++ others) : (make opens closes others h).word c = true := by
  simp only [word, make, hw, Bool.not_false, Bool.true_and, Bool.not_eq_true',
    decide_eq_false_iff_not]
  exact hn

end Lexicon

/-! ## Tokens -/

/-- Is this list of characters a token: one non-separator, or two or more word characters? -/
def isTokenChars (lex : Lexicon) : List Char → Bool
  | [] => false
  | [c] => !lex.sep c
  | c :: d :: cs => (c :: d :: cs).all lex.word

/-- Is `s` a token of the lexicon? Decidable, so token literals are discharged by `decide`. -/
def isToken (lex : Lexicon) (s : String) : Bool := isTokenChars lex s.toList

/-- A predicate-restricted string. -/
abbrev Restricted (P : String → Bool) : Type := { s : String // P s = true }

/-- **The token alphabet** of a lexicon. -/
abbrev Token (lex : Lexicon) : Type := Restricted (isToken lex)

instance {lex : Lexicon} : DecidableEq (Token lex) := Subtype.instDecidableEq

variable {lex : Lexicon}

/-- A string is empty exactly when its characters are. -/
theorem toList_eq_nil_iff {s : String} : s.toList = [] ↔ s = "" :=
  ⟨fun h => String.ext (by rw [h]; rfl), fun h => by rw [h]; rfl⟩

/-- A token's characters are never empty. -/
theorem Token.toList_ne_nil (t : Token lex) : t.val.toList ≠ [] := by
  intro h
  have := t.2
  simp only [isToken, h, isTokenChars] at this
  cases this

/-- A token contains no separator. -/
theorem Token.no_sep (t : Token lex) : ∀ c ∈ t.val.toList, lex.sep c = false := by
  have ht := t.2
  simp only [isToken] at ht
  intro c hc
  match hcs : t.val.toList, ht, hc with
  | [], _, hc => simp at hc
  | [x], ht, hc =>
      simp only [isTokenChars, Bool.not_eq_true'] at ht
      simp only [List.mem_singleton] at hc
      subst hc; exact ht
  | x :: y :: zs, ht, hc =>
      simp only [isTokenChars, List.all_eq_true] at ht
      exact Lexicon.word_sep (ht c hc)

/-- Tokens are equal exactly when their characters are. -/
theorem Token.eq_of_toList {t u : Token lex} (h : t.val.toList = u.val.toList) : t = u := by
  apply Subtype.ext
  apply String.ext
  exact h

/-- A run of word characters is a token. -/
theorem isTokenChars_of_word {w : List Char} (hw : ∀ c ∈ w, lex.word c = true) (hne : w ≠ []) :
    isTokenChars lex w = true := by
  match w, hw, hne with
  | [], _, hne => exact absurd rfl hne
  | [c], hw, _ =>
      simp only [isTokenChars, Bool.not_eq_true']
      exact Lexicon.word_sep (hw c (by simp))
  | c :: d :: cs, hw, _ =>
      simp only [isTokenChars, List.all_eq_true]
      exact hw

/-- A token from a non-empty run of word characters. -/
def Token.ofWord (w : List Char) (hw : ∀ c ∈ w, lex.word c = true) (hne : w ≠ []) : Token lex :=
  ⟨String.ofList w, by simp only [isToken, String.toList_ofList]; exact isTokenChars_of_word hw hne⟩

@[simp] theorem Token.ofWord_toList (w : List Char) (hw : ∀ c ∈ w, lex.word c = true)
    (hne : w ≠ []) : (Token.ofWord w hw hne : Token lex).val.toList = w := by
  simp [Token.ofWord, String.toList_ofList]

/-- A one-character token. -/
def Token.single (c : Char) (h : lex.sep c = false) : Token lex :=
  ⟨String.ofList [c], by simp [isToken, String.toList_ofList, isTokenChars, h]⟩

@[simp] theorem Token.single_toList (c : Char) (h : lex.sep c = false) :
    (Token.single c h : Token lex).val.toList = [c] := by
  simp [Token.single, String.toList_ofList]

/-! ## Self-delimiting tokens -/

/-- A token that is one self-delimiting character. -/
def Token.isPunct (t : Token lex) : Bool :=
  match t.val.toList with
  | [c] => lex.punct c
  | _ => false

/-- An opener: printed with no space after. -/
def Token.isOpen (t : Token lex) : Bool :=
  match t.val.toList with
  | [c] => lex.opens c
  | _ => false

/-- A closer: printed with no space before. -/
def Token.isClose (t : Token lex) : Bool :=
  match t.val.toList with
  | [c] => lex.closes c
  | _ => false

theorem Token.isPunct_of_isOpen {t : Token lex} (h : t.isOpen = true) : t.isPunct = true := by
  unfold Token.isOpen at h
  unfold Token.isPunct
  split at h
  · rename_i c _; exact lex.opens_punct c h
  · cases h

theorem Token.isPunct_of_isClose {t : Token lex} (h : t.isClose = true) : t.isPunct = true := by
  unfold Token.isClose at h
  unfold Token.isPunct
  split at h
  · rename_i c _; exact lex.closes_punct c h
  · cases h

/-- A token that is not self-delimiting consists of word characters. -/
theorem Token.word_of_not_isPunct {t : Token lex} (h : t.isPunct = false) :
    ∀ c ∈ t.val.toList, lex.word c = true := by
  have ht := t.2
  have hs := t.no_sep
  simp only [isToken] at ht
  intro c hc
  unfold Token.isPunct at h
  match hcs : t.val.toList, ht, hc, h with
  | [], _, hc, _ => simp at hc
  | [x], _, hc, h =>
      simp only [List.mem_singleton] at hc
      subst hc
      exact Lexicon.word_of (hs c (by rw [hcs]; simp)) h
  | x :: y :: zs, ht, hc, _ =>
      simp only [isTokenChars, List.all_eq_true] at ht
      exact ht c hc

/-- A self-delimiting token is one self-delimiting character. -/
theorem Token.eq_single_of_isPunct {t : Token lex} (h : t.isPunct = true) :
    ∃ c, t.val.toList = [c] ∧ lex.punct c = true := by
  unfold Token.isPunct at h
  split at h
  · rename_i c hc; exact ⟨c, hc, h⟩
  · cases h

/-- A token beginning with a self-delimiting character is that character alone. -/
theorem Token.isPunct_of_head {t : Token lex} {c : Char} (hh : t.val.toList.head? = some c)
    (hp : lex.punct c = true) : t.isPunct = true := by
  cases h : t.isPunct with
  | true => rfl
  | false =>
      have hw := Token.word_of_not_isPunct h c (by
        cases hcs : t.val.toList with
        | nil => rw [hcs] at hh; cases hh
        | cons x xs =>
            rw [hcs, List.head?_cons, Option.some.injEq] at hh
            subst hh; simp)
      rw [Lexicon.word_punct hw] at hp
      cases hp

end LambdaLab.Parser.IsoParser
