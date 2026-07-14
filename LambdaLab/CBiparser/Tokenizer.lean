import LambdaLab.CBiparser.Token
import LambdaLab.CBiparser.RoundTrip

/-!
# The tokenizer

Splits a character stream on maximal runs of separators. Parameterised by `sep : Char → Bool` and
nothing else — a tokenizer knows nothing about grammars.

## Residual tracking, and why

A token-level biparser hands back a leftover in `List (Token sep)`. To precompose it with this
tokenizer we need a leftover in `List Char` — and **a suffix of the token list does not determine a
suffix of the character list**, because the separators were thrown away (leftover tokens
`["b", "c"]` could have come from `"b c"` or from `"b     c"`). So the composite cannot be built by
a generic `bind`; the tokenizer has to be able to *replay* its own consumption.

`dropToks n` is that replay: the characters remaining after the first `n` tokens, **including the
separator run that precedes the next one**. That last detail is what makes the leftover come back
*exactly*, rather than with its leading whitespace eaten.

## The seam

`render` puts one separator *between* tokens and none at the end, so
`tokens (render ts ++ rest) = ts ++ tokens rest` needs a side condition: **`rest` is empty, or
begins with a separator**. Without it the continuation fuses onto the last rendered token
(`render ["a"] ++ "b"` tokenizes as `["ab"]`, not `["a", "b"]`).

That condition is exactly `HeadIn sep` — the *same* predicate the token-level laws use for FOLLOW,
now at the character level. And `HeadIn` is vacuous at `[]`, so the top-level (whole-file) round
trip pays nothing for it, just as `run_nil` made the token-level one free.
-/

namespace LambdaLab.CBiparser

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
  ⟨String.ofList w, by simpa [String.toList_ofList] using And.intro h1 h2⟩

@[simp] theorem Token.ofChars_toList (sep : Char → Bool) (w : List Char)
    (h1 : ∀ c ∈ w, sep c = false) (h2 : w ≠ []) :
    (Token.ofChars sep w h1 h2).val.toList = w := by
  simp [Token.ofChars, String.toList_ofList]

/-! ## Tokenizing -/

/-- The characters after the first token — **including the separators that precede the next one**.
This is the replay step: `dropToks` iterates it. -/
def afterFirstTok (sep : Char → Bool) (cs : List Char) : List Char :=
  afterWord sep (skipSep sep cs)

/-- The characters remaining after the first `n` tokens. -/
def dropToks (sep : Char → Bool) : Nat → List Char → List Char
  | 0, cs => cs
  | n + 1, cs => dropToks sep n (afterFirstTok sep cs)

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
          (by simp [word, List.takeWhile_cons, h]) ::
        tokens sep (afterWord sep (c :: cs))
  termination_by cs => cs.length
  decreasing_by
    · simp
    · have hc : sep c = false := by simpa using h
      have := length_dropWhile_le (fun x => !sep x) cs
      simp only [afterWord, List.dropWhile_cons, hc, Bool.not_false, if_pos, List.length_cons]
      omega

/-- A leading separator is skipped. -/
@[simp] theorem tokens_sep_cons {c : Char} (hc : sep c = true) (cs : List Char) :
    tokens sep (c :: cs) = tokens sep cs := by
  rw [tokens]; simp [hc]

theorem afterFirstTok_sep_cons {c : Char} (hc : sep c = true) (cs : List Char) :
    afterFirstTok sep (c :: cs) = afterFirstTok sep cs := by
  simp only [afterFirstTok, skipSep, List.dropWhile_cons, hc, if_pos]

/-! ## Rendering

One separator **between** tokens, none at the end. The trailing separator is deliberately omitted:
it would make the seam condition vacuous, but at the cost of printing a stray character after every
program. Paying the seam condition instead keeps `print` exact. -/

def render (sc : Char) : List (Token sep) → List Char
  | []      => []
  | [t]     => t.val.toList
  | t :: ts => t.val.toList ++ sc :: render sc ts

/-! ## The splitting lemmas

A token's characters, followed by anything that begins with a separator, split back off cleanly.
This is where non-emptiness and separator-freeness — both *in the type of `Token`* — get spent. -/

theorem takeWhile_append_word {w tail : List Char}
    (hw : ∀ c ∈ w, sep c = false) (ht : HeadIn sep tail) :
    (w ++ tail).takeWhile (fun c => !sep c) = w := by
  induction w with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a as =>
          have : sep a = true := ht a rfl
          simp [List.takeWhile_cons, this]
  | cons c w' ih =>
      have hc : sep c = false := hw c List.mem_cons_self
      simp [List.takeWhile_cons, hc, ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

theorem dropWhile_append_word {w tail : List Char}
    (hw : ∀ c ∈ w, sep c = false) (ht : HeadIn sep tail) :
    (w ++ tail).dropWhile (fun c => !sep c) = tail := by
  induction w with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a as =>
          have : sep a = true := ht a rfl
          simp [List.dropWhile_cons, this]
  | cons c w' ih =>
      have hc : sep c = false := hw c List.mem_cons_self
      simp [List.dropWhile_cons, hc, ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

/-- A token's characters never start with a separator, so nothing is skipped in front of them. -/
theorem skipSep_token (t : Token sep) (tail : List Char) :
    skipSep sep (t.val.toList ++ tail) = t.val.toList ++ tail := by
  cases hd : t.val.toList with
  | nil => exact absurd hd t.toList_ne_nil
  | cons c cs =>
      have hc : sep c = false := t.no_sep c (by rw [hd]; exact List.mem_cons_self)
      simp [skipSep, List.dropWhile_cons, hc]

/-- **A rendered token splits back off.** -/
theorem afterFirstTok_token (t : Token sep) {tail : List Char} (ht : HeadIn sep tail) :
    afterFirstTok sep (t.val.toList ++ tail) = tail := by
  rw [afterFirstTok, skipSep_token, afterWord]
  exact dropWhile_append_word t.no_sep ht

theorem tokens_token (t : Token sep) {tail : List Char} (ht : HeadIn sep tail) :
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

/-! ## The two laws the composition needs -/

/-- **Tokenizing a rendering.** The seam condition `HeadIn sep rest` is exactly "the continuation
is empty, or begins with a separator" — without it the continuation fuses onto the last token. -/
theorem tokens_render_append {sc : Char} (hsc : sep sc = true) :
    ∀ (ts : List (Token sep)) {rest : List Char}, HeadIn sep rest →
      tokens sep (render sc ts ++ rest) = ts ++ tokens sep rest := by
  intro ts
  induction ts with
  | nil => intro rest _; simp [render]
  | cons t ts ih =>
      intro rest hrest
      cases ts with
      | nil => simpa [render] using tokens_token t hrest
      | cons u us =>
          have hstep : render sc (t :: u :: us) ++ rest
              = t.val.toList ++ (sc :: (render sc (u :: us) ++ rest)) := by
            simp [render]
          rw [hstep, tokens_token t (by intro a ha; simp at ha; subst ha; exact hsc),
            tokens_sep_cons hsc, ih hrest]
          simp

/-- **Replaying the consumption.** After the `ts` tokens, exactly `rest` characters remain — with
their leading separators intact, which is the whole point of `afterFirstTok`. -/
theorem dropToks_render {sc : Char} (hsc : sep sc = true) :
    ∀ (ts : List (Token sep)) {rest : List Char}, HeadIn sep rest →
      dropToks sep ts.length (render sc ts ++ rest) = rest := by
  intro ts
  induction ts with
  | nil => intro rest _; simp [render, dropToks]
  | cons t ts ih =>
      intro rest hrest
      cases ts with
      | nil =>
          simp only [render, List.length_cons, List.length_nil, dropToks]
          rw [afterFirstTok_token t hrest]
      | cons u us =>
          have hstep : render sc (t :: u :: us) ++ rest
              = t.val.toList ++ (sc :: (render sc (u :: us) ++ rest)) := by
            simp [render]
          simp only [List.length_cons, dropToks]
          rw [hstep, afterFirstTok_token t (by intro a ha; simp at ha; subst ha; exact hsc),
            afterFirstTok_sep_cons hsc]
          exact ih hrest

end LambdaLab.CBiparser
