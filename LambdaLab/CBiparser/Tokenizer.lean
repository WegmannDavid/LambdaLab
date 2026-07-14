import LambdaLab.CBiparser.Token
import LambdaLab.CBiparser.Basic
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
  ⟨String.ofList w, isToken_iff.mpr (by rw [String.toList_ofList]; exact ⟨h1, h2⟩)⟩

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

/-! ## Progress: the replay strictly shrinks the input -/

theorem length_afterFirstTok_le (cs : List Char) :
    (afterFirstTok sep cs).length ≤ cs.length :=
  Nat.le_trans (length_dropWhile_le _ _) (length_dropWhile_le _ _)

/-- If there *is* a token, consuming it costs at least one character. This is where
**non-emptiness of `Token`** pays for the composite's progress proof. -/
theorem length_afterFirstTok_lt : ∀ {cs : List Char}, tokens sep cs ≠ [] →
    (afterFirstTok sep cs).length < cs.length
  | [], h => by simp [tokens] at h
  | c :: cs, h => by
      by_cases hc : sep c = true
      · have ih := length_afterFirstTok_lt (cs := cs) (by rwa [tokens_sep_cons hc] at h)
        rw [afterFirstTok_sep_cons hc]
        simp only [List.length_cons]
        omega
      · have hcf : sep c = false := by simpa using hc
        have h1 : skipSep sep (c :: cs) = c :: cs := by simp [skipSep, List.dropWhile_cons, hcf]
        have h2 : afterWord sep (c :: cs) = afterWord sep cs := by
          simp [afterWord, List.dropWhile_cons, hcf]
        have h3 := length_dropWhile_le (fun x => !sep x) cs
        have h4 : afterFirstTok sep (c :: cs) = afterWord sep cs := by
          simp only [afterFirstTok, h1, h2]
        have h5 : (afterFirstTok sep (c :: cs)).length ≤ cs.length :=
          Nat.le_trans (Nat.le_of_eq (congrArg List.length h4)) h3
        simp only [List.length_cons]
        omega

theorem length_dropToks_le : ∀ (n : Nat) (cs : List Char),
    (dropToks sep n cs).length ≤ cs.length
  | 0, cs => by simp [dropToks]
  | n + 1, cs => by
      simp only [dropToks]
      exact Nat.le_trans (length_dropToks_le n _) (length_afterFirstTok_le cs)

theorem length_dropToks_lt {n : Nat} {cs : List Char} (hn : 0 < n) (h : tokens sep cs ≠ []) :
    (dropToks sep n cs).length < cs.length := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [dropToks]
      exact Nat.lt_of_le_of_lt (length_dropToks_le m _) (length_afterFirstTok_lt h)

/-! ## The composite

`viaTokens` precomposes a token-level biparser with the tokenizer: `parse` tokenizes, runs the
inner parser, then **replays** its consumption with `dropToks` to recover a *character* leftover.
`print` renders. -/

/-- Precompose a token-level biparser with the tokenizer. -/
def viaTokens {w v : Type} (sep : Char → Bool) (sc : Char)
    (P : CBiparser (Token sep) w v) : CBiparser Char w v where
  parse cs :=
    (P.parse (tokens sep cs)).map (fun r =>
      (r.1, ⟨dropToks sep ((tokens sep cs).length - r.2.val.length) cs, by
        refine length_dropToks_lt ?_ ?_
        · have := r.2.2; omega
        · intro hnil
          -- `r`'s TYPE mentions `tokens sep cs`, so rewriting it there is not type correct;
          -- go through the length instead
          have h2 := r.2.2
          have hz : (tokens sep cs).length = 0 := by rw [hnil]; rfl
          omega⟩))
  print x := ((P.print x).1, render sc (P.print x).2)

/-- The **erased-level** equation for the composite. Stating the law against `run` keeps the
strict-suffix subtype out of every proof — and here it is not merely convenient but *necessary*:
the subtype's proof mentions `tokens sep cs`, so rewriting that term underneath `parse` is not
type correct. -/
theorem viaTokens_run {w v : Type} (sep : Char → Bool) (sc : Char)
    (P : CBiparser (Token sep) w v) (cs : List Char) :
    (viaTokens sep sc P).run cs
      = (P.run (tokens sep cs)).map
          (fun r => (r.1, dropToks sep ((tokens sep cs).length - r.2.length) cs)) := by
  simp only [CBiparser.run, viaTokens, Option.map_map]
  cases P.parse (tokens sep cs) <;> rfl

/-- **The composite FOLLOW.** Two seams, honestly stated: the continuation must begin with a
separator (or be empty), *and* its first **token** must lie in the inner parser's FOLLOW.

This is **not** of the form `HeadIn f` for any `f : Char → Bool`, and it cannot be: one character
of lookahead does not determine the next *token*, because the next character may be whitespace.
That is a real fact about two-stage lexing, not a defect — and it is why the composite is a
`CBiparser` rather than an `IBip`. At the top level (`rest = []`) both halves are vacuous, so the
whole-file round trip pays nothing. -/
def CharFollow (sep : Char → Bool) (fol : Token sep → Bool) (rest : List Char) : Prop :=
  HeadIn sep rest ∧ HeadIn fol (tokens sep rest)

/-- **The composed round-trip law.** -/
theorem viaTokens_roundTrips {w v : Type} {sep : Char → Bool} {sc : Char} (hsc : sep sc = true)
    {fol : Token sep → Bool} (P : CBiparser (Token sep) w v)
    (hP : RoundTrips P (HeadIn fol)) :
    RoundTrips (viaTokens sep sc P) (CharFollow sep fol) := by
  intro x rest hF
  obtain ⟨hsep, htok⟩ := hF
  have htoks : tokens sep (render sc (P.print x).2 ++ rest)
      = (P.print x).2 ++ tokens sep rest := tokens_render_append hsc _ hsep
  have hinner : P.run ((P.print x).2 ++ tokens sep rest)
      = some ((P.print x).1, tokens sep rest) := hP x _ htok
  rw [viaTokens_run]
  simp only [viaTokens]
  rw [htoks, hinner]
  simp only [Option.map_some, List.length_append, Nat.add_sub_cancel]
  rw [dropToks_render hsc _ hsep]

/-- **The payoff: a whole file round-trips, with no side condition at all.** Both seams are vacuous
at end of input. -/
theorem viaTokens_roundtrip {w v : Type} {sep : Char → Bool} {sc : Char} (hsc : sep sc = true)
    {fol : Token sep → Bool} (P : CBiparser (Token sep) w v)
    (hP : RoundTrips P (HeadIn fol)) (x : w) :
    (viaTokens sep sc P).run ((viaTokens sep sc P).print x).2
      = some (((viaTokens sep sc P).print x).1, []) := by
  have h := viaTokens_roundTrips hsc P hP x [] ⟨by simp, by simp [tokens]⟩
  simpa using h

end LambdaLab.CBiparser
