import LambdaLab.IsoParser.Token
import LambdaLab.IsoParser.Basic

/-!
# The tokenizer — forward direction

Splits a character stream on maximal runs of separators. Parameterised by `sep : Char → Bool` and
nothing else — a tokenizer knows nothing about grammars.

This is the salvaged core of the deleted `CBiparser/Tokenizer.lean`: the `tokens` function and its
splitting laws only. The residual-tracking machinery (`dropToks`, `viaTokens`) that composed it
with token-level biparsers is deliberately not ported — whole-artifact pipeline stages
(`Abstraction2/Tokenizer.lean`) compose by `Option.bind` and never need a replayable leftover.

## The seam

`tokens (t.toList ++ tail) = t :: tokens tail` needs a side condition: **`tail` is empty, or begins
with a separator** — else the continuation fuses onto the token. That condition is exactly
`HeadIn (sep · = true)` from `IsoParser/Basic.lean` — the same predicate the token-level laws use
for FOLLOW, now at the character level. It is vacuous at `[]`, so whole-input uses pay nothing.

Both invariants in the `Token` type get spent here: separator-freeness makes a token's characters
split back off (`takeWhile_append_word`), non-emptiness stops a token from vanishing
(`tokens_token`'s head case).
-/

namespace LambdaLab.IsoParser

variable {sep : Char → Bool}

/-! ## Words -/

/-- The characters of the next token: the maximal separator-free prefix. -/
def word (sep : Char → Bool) (cs : List Char) : List Char :=
  cs.takeWhile (fun c => !sep c)

/-- What follows the next token's characters. -/
def afterWord (sep : Char → Bool) (cs : List Char) : List Char :=
  cs.dropWhile (fun c => !sep c)

/-- Skip a run of separators. -/
def skipSep (sep : Char → Bool) (cs : List Char) : List Char :=
  cs.dropWhile sep

/-- The head of a `dropWhile` fails the predicate. -/
theorem dropWhile_head_false {α : Type} {p : α → Bool} :
    ∀ {l : List α} {a t}, l.dropWhile p = a :: t → p a = false
  | [], a, t, h => by simp [List.dropWhile] at h
  | b :: bs, a, t, h => by
      rw [List.dropWhile_cons] at h
      split at h
      · exact dropWhile_head_false h
      · rename_i hp
        have : a = b := by cases h; rfl
        rw [this]; simpa using hp

/-- Membership in a `takeWhile` satisfies the predicate. -/
theorem mem_takeWhile {α : Type} {p : α → Bool} :
    ∀ {l : List α} {a}, a ∈ l.takeWhile p → p a = true
  | [], a, h => by simp [List.takeWhile] at h
  | b :: bs, a, h => by
      rw [List.takeWhile_cons] at h
      split at h
      · rename_i hp
        rcases List.mem_cons.mp h with rfl | h'
        · exact hp
        · exact mem_takeWhile h'
      · simp at h

theorem length_dropWhile_le {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => by simp
  | a :: as => by
      rw [List.dropWhile_cons]
      split
      · exact Nat.le_succ_of_le (length_dropWhile_le p as)
      · simp

/-- Build a token from characters known to be separator-free and non-empty. -/
def Token.ofChars (sep : Char → Bool) (w : List Char)
    (h1 : ∀ c ∈ w, sep c = false) (h2 : w ≠ []) : Token sep :=
  ⟨String.ofList w, isToken_iff.mpr (by rw [String.toList_ofList]; exact ⟨h1, h2⟩)⟩

@[simp] theorem Token.ofChars_toList (sep : Char → Bool) (w : List Char)
    (h1 : ∀ c ∈ w, sep c = false) (h2 : w ≠ []) :
    (Token.ofChars sep w h1 h2).val.toList = w := by
  simp [Token.ofChars, String.toList_ofList]

/-! ## Tokenizing -/

/-- **The tokenizer.** Split on maximal separator runs; every token is non-empty and
separator-free *by construction*, so the invariant never has to be re-established.

Recursing directly on characters (rather than on `skipSep`) is what makes `tokens_sep_cons` below
a one-liner — and that lemma is used in every subsequent proof. -/
def tokens (sep : Char → Bool) : List Char → List (Token sep)
  | [] => []
  | c :: cs =>
      if h : sep c = true then
        tokens sep cs
      else
        Token.ofChars sep (word sep (c :: cs))
          (fun x hx => by simpa using mem_takeWhile (p := fun y => !sep y) hx)
          (by simp [word, h]) ::
        tokens sep (afterWord sep (c :: cs))
  termination_by cs => cs.length
  decreasing_by
    · simp
    · have hc : sep c = false := by simpa using h
      have := length_dropWhile_le (fun x => !sep x) cs
      simp only [afterWord, List.dropWhile_cons, hc, Bool.not_false, if_pos, List.length_cons]
      omega

theorem tokens_nil : tokens sep [] = [] := by simp [tokens]

/-- A leading separator is skipped. -/
@[simp] theorem tokens_sep_cons {c : Char} (hc : sep c = true) (cs : List Char) :
    tokens sep (c :: cs) = tokens sep cs := by
  rw [tokens]; simp [hc]

/-- An all-separator string tokenizes to nothing. -/
theorem tokens_all_sep {g : List Char} (h : ∀ c ∈ g, sep c = true) : tokens sep g = [] := by
  induction g with
  | nil => exact tokens_nil
  | cons c g' ih =>
      rw [tokens_sep_cons (h c List.mem_cons_self)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- An all-separator string satisfies the seam condition. -/
theorem headIn_of_allSep {g : List Char} (h : ∀ c ∈ g, sep c = true) :
    HeadIn (fun c => sep c = true) g := by
  intro a ha
  cases g with
  | nil => simp at ha
  | cons c cs =>
      rw [List.head?_cons] at ha
      simp only [Option.some.injEq] at ha; subst ha
      exact h c List.mem_cons_self

/-! ## The splitting lemmas

A token's characters, followed by anything that begins with a separator, split back off cleanly.
This is where non-emptiness and separator-freeness — both *in the type of `Token`* — get spent. -/

theorem takeWhile_append_word {w tail : List Char}
    (hw : ∀ c ∈ w, sep c = false) (ht : HeadIn (fun c => sep c = true) tail) :
    (w ++ tail).takeWhile (fun c => !sep c) = w := by
  induction w with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a as =>
          have : sep a = true := ht a rfl
          simp [this]
  | cons c w' ih =>
      have hc : sep c = false := hw c List.mem_cons_self
      simp [hc, ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

theorem dropWhile_append_word {w tail : List Char}
    (hw : ∀ c ∈ w, sep c = false) (ht : HeadIn (fun c => sep c = true) tail) :
    (w ++ tail).dropWhile (fun c => !sep c) = tail := by
  induction w with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a as =>
          have : sep a = true := ht a rfl
          simp [this]
  | cons c w' ih =>
      have hc : sep c = false := hw c List.mem_cons_self
      simp [hc, ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

/-- **A rendered token splits back off.** -/
theorem tokens_token (t : Token sep) {tail : List Char}
    (ht : HeadIn (fun c => sep c = true) tail) :
    tokens sep (t.val.toList ++ tail) = t :: tokens sep tail := by
  cases hd : t.val.toList with
  | nil => exact absurd hd t.toList_ne_nil
  | cons c cs =>
      have hc : sep c = false := t.no_sep c (by rw [hd]; exact List.mem_cons_self)
      have hall : ∀ x ∈ t.val.toList, sep x = false := t.no_sep
      rw [List.cons_append, tokens]
      simp only [dif_neg (by simp [hc] : ¬ (sep c = true))]
      have hw : word sep (c :: (cs ++ tail)) = t.val.toList := by
        rw [word, ← List.cons_append, ← hd]
        exact takeWhile_append_word hall ht
      have haw : afterWord sep (c :: (cs ++ tail)) = tail := by
        rw [afterWord, ← List.cons_append, ← hd]
        exact dropWhile_append_word hall ht
      rw [haw]
      congr 1
      exact Token.eq_of_toList (by rw [Token.ofChars_toList, hw])

/-- Tokenizing ignores a leading run of separators. -/
theorem tokens_sep_prepend {g cs : List Char} (hg : ∀ c ∈ g, sep c = true) :
    tokens sep (g ++ cs) = tokens sep cs := by
  induction g with
  | nil => rfl
  | cons c g' ih =>
      rw [List.cons_append, tokens_sep_cons (hg c List.mem_cons_self),
        ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))]

end LambdaLab.IsoParser
