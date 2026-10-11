import LambdaLab.Parser.IsoParser.Token
import LambdaLab.Parser.IsoParser.Basic

/-!
# The tokenizer — forward direction

Splits a character stream into the tokens of a `Lexicon`: separators are skipped, a
self-delimiting character is a token by itself, and a maximal run of word characters is one token.
A tokenizer knows nothing about grammars.

## The seam

`tokens (t.toList ++ tail) = t :: tokens tail` needs a side condition, or the continuation fuses
onto the token: **`t` is self-delimiting, or `tail` is empty or begins with a character that cannot
continue a word** — a separator or a self-delimiting character. The second half is
`HeadIn (word · = false)`, the same predicate the token-level laws use for FOLLOW, now at the
character level. It is vacuous at `[]`, so whole-input uses pay nothing.

The invariants in the `Token` type get spent here: a word token's characters split back off
(`takeWhile_append_word`), a self-delimiting token is one character, and non-emptiness stops a token
from vanishing.
-/

namespace LambdaLab.Parser.IsoParser

variable {lex : Lexicon}

/-! ## Words -/

/-- The characters of the next word token: the maximal run of word characters. -/
def word (lex : Lexicon) (cs : List Char) : List Char := cs.takeWhile lex.word

/-- What follows the next word token's characters. -/
def afterWord (lex : Lexicon) (cs : List Char) : List Char := cs.dropWhile lex.word

/-- Skip a run of separators. -/
def skipSep (lex : Lexicon) (cs : List Char) : List Char := cs.dropWhile lex.sep

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

/-! ## Tokenizing -/

/-- **The tokenizer.** Skip separators; a self-delimiting character is a token by itself; otherwise
take the maximal run of word characters. Every token is well-formed *by construction*. -/
def tokens (lex : Lexicon) : List Char → List (Token lex)
  | [] => []
  | c :: cs =>
      if hs : lex.sep c = true then
        tokens lex cs
      else if hp : lex.punct c = true then
        Token.single c (by simpa using hs) :: tokens lex cs
      else
        Token.ofWord (word lex (c :: cs)) (fun x hx => mem_takeWhile hx)
          (by simp [word, Lexicon.word, show lex.sep c = false by simpa using hs,
            show lex.punct c = false by simpa using hp]) ::
        tokens lex (afterWord lex (c :: cs))
  termination_by cs => cs.length
  decreasing_by
    · simp
    · simp
    · have hw : lex.word c = true :=
        Lexicon.word_of (by simpa using hs) (by simpa using hp)
      have := length_dropWhile_le lex.word cs
      simp only [afterWord, List.dropWhile_cons, hw, if_pos, List.length_cons]
      omega

theorem tokens_nil : tokens lex [] = [] := by simp [tokens]

/-- A leading separator is skipped. -/
@[simp] theorem tokens_sep_cons {c : Char} (hc : lex.sep c = true) (cs : List Char) :
    tokens lex (c :: cs) = tokens lex cs := by
  rw [tokens]; simp [hc]

/-- A self-delimiting character is a token by itself. -/
theorem tokens_punct_cons {c : Char} (hp : lex.punct c = true) (cs : List Char) :
    tokens lex (c :: cs) =
      Token.single c (by
        cases h : lex.sep c with
        | false => rfl
        | true => rw [lex.sep_punct c h] at hp; cases hp) :: tokens lex cs := by
  have hs : lex.sep c = false := by
    cases h : lex.sep c with
    | false => rfl
    | true => rw [lex.sep_punct c h] at hp; cases hp
  rw [tokens]
  simp [hs, hp]

/-- An all-separator string tokenizes to nothing. -/
theorem tokens_all_sep {g : List Char} (h : ∀ c ∈ g, lex.sep c = true) : tokens lex g = [] := by
  induction g with
  | nil => exact tokens_nil
  | cons c g' ih =>
      rw [tokens_sep_cons (h c List.mem_cons_self)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- An all-separator string ends a word. -/
theorem headIn_of_allSep {g : List Char} (h : ∀ c ∈ g, lex.sep c = true) :
    HeadIn (fun c => lex.word c = false) g := by
  intro a ha
  cases g with
  | nil => simp at ha
  | cons c cs =>
      rw [List.head?_cons] at ha
      have hca : c = a := Option.some.inj ha
      have hc : lex.sep a = true := hca ▸ h c List.mem_cons_self
      simp [Lexicon.word, hc]

/-! ## The splitting lemmas -/

theorem takeWhile_append_word {w tail : List Char}
    (hw : ∀ c ∈ w, lex.word c = true) (ht : HeadIn (fun c => lex.word c = false) tail) :
    (w ++ tail).takeWhile lex.word = w := by
  induction w with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a as =>
          have : lex.word a = false := ht a rfl
          simp [this]
  | cons c w' ih =>
      have hc : lex.word c = true := hw c List.mem_cons_self
      simp [hc, ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

theorem dropWhile_append_word {w tail : List Char}
    (hw : ∀ c ∈ w, lex.word c = true) (ht : HeadIn (fun c => lex.word c = false) tail) :
    (w ++ tail).dropWhile lex.word = tail := by
  induction w with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a as =>
          have : lex.word a = false := ht a rfl
          simp [this]
  | cons c w' ih =>
      have hc : lex.word c = true := hw c List.mem_cons_self
      simp [hc, ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

/-- **A rendered token splits back off**, when it is self-delimiting or what follows cannot
continue it. -/
theorem tokens_token (t : Token lex) {tail : List Char}
    (h : t.isPunct = true ∨ HeadIn (fun c => lex.word c = false) tail) :
    tokens lex (t.val.toList ++ tail) = t :: tokens lex tail := by
  cases hp : t.isPunct with
  | true =>
      obtain ⟨c, hc, hpc⟩ := Token.eq_single_of_isPunct hp
      rw [hc, List.singleton_append, tokens_punct_cons hpc]
      congr 1
      exact Token.eq_of_toList (by simp [hc])
  | false =>
      have ht : HeadIn (fun c => lex.word c = false) tail := by
        rcases h with h | h
        · rw [hp] at h; cases h
        · exact h
      have hw := Token.word_of_not_isPunct hp
      cases hd : t.val.toList with
      | nil => exact absurd hd t.toList_ne_nil
      | cons c cs =>
          have hcw : lex.word c = true := hw c (by rw [hd]; exact List.mem_cons_self)
          rw [List.cons_append, tokens]
          simp only [dif_neg (by simp [Lexicon.word_sep hcw] : ¬ (lex.sep c = true)),
            dif_neg (by simp [Lexicon.word_punct hcw] : ¬ (lex.punct c = true))]
          have hwd : word lex (c :: (cs ++ tail)) = t.val.toList := by
            rw [word, ← List.cons_append, ← hd]
            exact takeWhile_append_word hw ht
          have haw : afterWord lex (c :: (cs ++ tail)) = tail := by
            rw [afterWord, ← List.cons_append, ← hd]
            exact dropWhile_append_word hw ht
          rw [haw]
          congr 1
          exact Token.eq_of_toList (by rw [Token.ofWord_toList, hwd])

/-- Tokenizing ignores a leading run of separators. -/
theorem tokens_sep_prepend {g cs : List Char} (hg : ∀ c ∈ g, lex.sep c = true) :
    tokens lex (g ++ cs) = tokens lex cs := by
  induction g with
  | nil => rfl
  | cons c g' ih =>
      rw [List.cons_append, tokens_sep_cons (hg c List.mem_cons_self),
        ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))]

end LambdaLab.Parser.IsoParser
