import LambdaLab.Abstraction.Basic
import LambdaLab.Parser.IsoParser.Tokenize

/-!
# The tokenizer as a morphism of `Abs` — the archetypal lossless stage

`List Char ⇝ List Token`, for a `Lexicon`. The lossy map is `tokens` (tokenize), which forgets the
separators; the **annotation over a token sequence `ts` is exactly the gaps** — the separator runs
that, interleaved with `ts`, reconstruct a character string tokenizing to `ts`:

```
lead · t₁ · g₁ · t₂ · … · gₙ₋₁ · tₙ · trail
```

`lead`/`trail` may be empty. An interior gap `gᵢ` may be empty **only when `tᵢ` or `tᵢ₊₁` is
self-delimiting** — two word tokens with nothing between them would fuse into one, but `f` and `(`
may touch. Encoding that *in the type* (`Gap`) is what makes `abstract_realize` — tokenize the
reconstruction and recover `ts` — go through.

Tokenizing never fails, so `abstract` is `some ∘ tokens`; and the tokenizer forgets *only* the
gaps, so it is the archetypal **lossless** stage: every string is the realization of the gaps read
off it (`realize_complete_aux`, which discharges the `lossless` field).

## The canonical layout

`defaultInner` spaces a token list the way the lexicon asks: nothing after an opener, nothing
before a closer, one space everywhere else (`canonGap`). So with `(` an opener and `)` a closer,
`f ( x )` prints as `f (x)`. A lexicon with no self-delimiting characters spaces every gap.
-/

namespace LambdaLab.Abstraction

open LambdaLab.Parser.IsoParser

variable {lex : Lexicon}

/-- A possibly-empty run of separators. -/
def SepRun (lex : Lexicon) : Type := { g : List Char // ∀ c ∈ g, lex.sep c = true }

/-- A non-empty run of separators. -/
def NEGap (lex : Lexicon) : Type := { g : List Char // g ≠ [] ∧ ∀ c ∈ g, lex.sep c = true }

def NEGap.toSepRun (g : NEGap lex) : SepRun lex := ⟨g.1, g.2.2⟩

/-- **What may stand between `t` and `u`**: separators — at least one, unless one of the two is
self-delimiting. -/
def Gap (lex : Lexicon) (t u : Token lex) : Type :=
  { g : List Char // (∀ c ∈ g, lex.sep c = true) ∧ (g ≠ [] ∨ t.isPunct = true ∨ u.isPunct = true) }

/-- A non-empty run may stand between any two tokens. -/
def NEGap.toGap (g : NEGap lex) (t u : Token lex) : Gap lex t u := ⟨g.1, g.2.2, .inl g.2.1⟩

theorem head?_append_ne {α : Type} {l : List α} (h : l ≠ []) (l' : List α) :
    (l ++ l').head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- The gaps *after the leading run* for a token list: nothing for `[]`, a trailing run for a single
token, and a gap before each further token. -/
def Inner (lex : Lexicon) : List (Token lex) → Type
  | []            => PUnit
  | [_]           => SepRun lex
  | t :: u :: rest => Gap lex t u × Inner lex (u :: rest)

/-- The annotation over `ts`: a leading run plus the interior/trailing gaps. -/
structure Gaps (lex : Lexicon) (ts : List (Token lex)) where
  leading : SepRun lex
  inner : Inner lex ts

/-! ## Realization: interleave the tokens with their gaps -/

def realizeInner (lex : Lexicon) : (ts : List (Token lex)) → Inner lex ts → List Char
  | [],             _  => []
  | [t],            tr => t.val.toList ++ tr.val
  | t :: u :: rest, gi => t.val.toList ++ gi.1.val ++ realizeInner lex (u :: rest) gi.2

/-- Reconstruct the character string from a token list and its gaps. -/
def Gaps.realize {ts : List (Token lex)} (g : Gaps lex ts) : List Char :=
  g.leading.val ++ realizeInner lex ts g.inner

theorem realizeInner_head {v : Token lex} {vs : List (Token lex)} (inner : Inner lex (v :: vs)) :
    (realizeInner lex (v :: vs) inner).head? = v.val.toList.head? := by
  cases vs with
  | nil => exact head?_append_ne v.toList_ne_nil _
  | cons v2 vs2 =>
      show (v.val.toList ++ (inner.1.val) ++ realizeInner lex (v2 :: vs2) inner.2).head? = _
      rw [List.append_assoc]; exact head?_append_ne v.toList_ne_nil _

/-! ## Canonical gaps -/

/-- The one-character separator run `[sc]`. -/
def scGap (sc : Char) (hsc : lex.sep sc = true) : NEGap lex :=
  ⟨[sc], by
    refine ⟨by simp, ?_⟩
    intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact hsc⟩

/-- The empty separator run. -/
def emptyRun : SepRun lex := ⟨[], by intro c hc; simp at hc⟩

/-- **The canonical gap**: nothing after an opener or before a closer, one space otherwise. -/
def canonGap (lex : Lexicon) (t u : Token lex) : Gap lex t u :=
  if h : t.isOpen = true ∨ u.isClose = true then
    ⟨[], by intro c hc; simp at hc,
      .inr (h.elim (fun h => .inl (Token.isPunct_of_isOpen h))
        (fun h => .inr (Token.isPunct_of_isClose h)))⟩
  else (scGap ' ' lex.space_sep).toGap t u

/-- The canonical layout of a token list: canonical gaps between tokens, nothing at the ends. -/
def defaultInner (lex : Lexicon) : (ts : List (Token lex)) → Inner lex ts
  | []           => PUnit.unit
  | [_]          => emptyRun
  | t :: u :: us => (canonGap lex t u, defaultInner lex (u :: us))

/-! ## Gaps for a concatenation

The printers above this file emit a token stream as *blocks* — one per declaration — concatenated.
Gaps decompose the same way, which is what lets a canonical layout be assembled where the block
structure is known rather than guessed from token content. A non-empty `joint` may stand between
any two tokens, so it can join any two blocks.

`Inner` keeps the *trailing* run in its last token's slot, so joining replaces the left block's
trailing run with `joint`. Nothing is lost that anyone had: this builds a canonical annotation, it
does not transport a recorded one. -/

/-- Gaps for `ts ++ us`: the left block's own gaps, then `joint` at the seam, then the right
block's. -/
def joinInner (joint : NEGap lex) : (ts : List (Token lex)) → Inner lex ts →
    (us : List (Token lex)) → Inner lex us → Inner lex (ts ++ us)
  | [],           _,  _,      iu => iu
  | [_],          tr, [],     _  => tr
  | [t],          _,  u :: _, iu => (joint.toGap t u, iu)
  | _ :: v :: vs, it, us,     iu => (it.1, joinInner joint (v :: vs) it.2 us iu)

/-! ## `abstract ∘ realize = some ts`

Rendering the gaps and re-tokenizing recovers `ts`: the leading run is skipped, and each token is
peeled off because what follows it cannot continue it — a separator, or, across an empty gap, a
self-delimiting token on one side or the other. -/

theorem tokens_realizeInner : ∀ (ts : List (Token lex)) (inner : Inner lex ts),
    tokens lex (realizeInner lex ts inner) = ts
  | [],           _  => by rw [show realizeInner lex [] _ = [] from rfl]; exact tokens_nil
  | [t],          tr => by
      rw [show realizeInner lex [t] tr = t.val.toList ++ (tr : SepRun lex).val from rfl,
        tokens_token t (.inr (headIn_of_allSep tr.2)), tokens_all_sep tr.2]
  | t :: u :: us, gi => by
      have hg : ∀ c ∈ (gi.1 : Gap lex t u).val, lex.sep c = true := gi.1.2.1
      have hrw : realizeInner lex (t :: u :: us) gi
          = t.val.toList ++ (gi.1.val ++ realizeInner lex (u :: us) gi.2) := by
        simp [realizeInner, List.append_assoc]
      have hstop : t.isPunct = true ∨
          HeadIn (fun c => lex.word c = false) (gi.1.val ++ realizeInner lex (u :: us) gi.2) := by
        cases hv : gi.1.val with
        | cons x xs =>
            refine .inr (fun a ha => ?_)
            rw [List.cons_append, List.head?_cons, Option.some.injEq] at ha
            subst ha
            have hx : lex.sep x = true := hg x (by rw [hv]; exact List.mem_cons_self)
            simp [Lexicon.word, hx]
        | nil =>
            have hok := gi.1.2.2
            rw [hv] at hok
            rcases hok with hne | ht | hu
            · exact absurd rfl hne
            · exact .inl ht
            · refine .inr (fun a ha => ?_)
              rw [List.nil_append, realizeInner_head] at ha
              obtain ⟨c, hc, hpc⟩ := Token.eq_single_of_isPunct hu
              rw [hc, List.head?_cons, Option.some.injEq] at ha
              subst ha
              simp [Lexicon.word, hpc]
      rw [hrw, tokens_token t hstop, tokens_sep_prepend hg, tokens_realizeInner (u :: us) gi.2]

/-! ## `realize` is surjective onto every character string (faithful decomposition)

Every `cs` is the realization of the gaps read off it: the leading separators, then each token
followed by the separators after it. This discharges `lossless`. -/

/-- Whether `gap` may stand between `t` and the first token of `ts`. -/
def GapOk (t : Token lex) (gap : List Char) (ts : List (Token lex)) : Prop :=
  ∀ u us, ts = u :: us → gap ≠ [] ∨ t.isPunct = true ∨ u.isPunct = true

/-- Prepend a token `t` (with a new leading run) in front of the gaps for `ts`. The old leading run
becomes the gap after `t`. -/
def consInner (t : Token lex) (gap : SepRun lex) :
    (ts : List (Token lex)) → Inner lex ts → GapOk t gap.val ts → Inner lex (t :: ts)
  | [],      _,     _  => gap
  | u :: us, inner, ok => (⟨gap.val, gap.2, ok u us rfl⟩, inner)

def consGaps (t : Token lex) (newLead : SepRun lex) {ts : List (Token lex)} (g' : Gaps lex ts)
    (ok : GapOk t g'.leading.val ts) : Gaps lex (t :: ts) :=
  ⟨newLead, consInner t g'.leading ts g'.inner ok⟩

theorem realize_consGaps (t : Token lex) (newLead : SepRun lex) {ts : List (Token lex)}
    (g' : Gaps lex ts) (ok : GapOk t g'.leading.val ts) :
    Gaps.realize (consGaps t newLead g' ok)
      = newLead.val ++ (t.val.toList ++ Gaps.realize g') := by
  cases ts with
  | nil => simp [Gaps.realize, consGaps, consInner, realizeInner]
  | cons v vs => simp [Gaps.realize, consGaps, consInner, realizeInner, List.append_assoc]

/-- With an empty leading run, a realization starts with its first token's first character. -/
theorem realize_head_of_emptyLead {ts : List (Token lex)} (g : Gaps lex ts)
    (hl : g.leading.val = []) {u : Token lex} {us : List (Token lex)} (hts : ts = u :: us) :
    (Gaps.realize g).head? = u.val.toList.head? := by
  subst hts
  rw [Gaps.realize, hl, List.nil_append]
  exact realizeInner_head g.inner

theorem realize_complete_aux (cs : List Char) :
    ∃ g : Gaps lex (tokens lex cs), Gaps.realize g = cs := by
  have hlead : ∀ c ∈ cs.takeWhile lex.sep, lex.sep c = true := fun c hc => mem_takeWhile hc
  have hsplit : cs.takeWhile lex.sep ++ skipSep lex cs = cs := List.takeWhile_append_dropWhile
  have htcs : tokens lex cs = tokens lex (skipSep lex cs) := by
    calc tokens lex cs = tokens lex (cs.takeWhile lex.sep ++ skipSep lex cs) := by rw [hsplit]
      _ = tokens lex (skipSep lex cs) := tokens_sep_prepend hlead
  cases hrest : skipSep lex cs with
  | nil =>
      have htk : tokens lex cs = [] := by rw [htcs, hrest]; exact tokens_nil
      rw [htk]
      refine ⟨⟨⟨cs.takeWhile lex.sep, hlead⟩, PUnit.unit⟩, ?_⟩
      show cs.takeWhile lex.sep ++ realizeInner lex [] PUnit.unit = cs
      have hdrop : cs.dropWhile lex.sep = [] := hrest
      simp only [realizeInner, List.append_nil]
      calc cs.takeWhile lex.sep = cs.takeWhile lex.sep ++ cs.dropWhile lex.sep := by
            rw [hdrop, List.append_nil]
        _ = cs := List.takeWhile_append_dropWhile
  | cons c rest' =>
      have hcs : lex.sep c = false :=
        dropWhile_head_false (p := lex.sep) (l := cs) (a := c) (t := rest')
          (by rw [skipSep] at hrest; exact hrest)
      by_cases hp : lex.punct c = true
      · -- a self-delimiting character: a token by itself, and any gap may follow it
        have htcs2 : tokens lex cs = Token.single c hcs :: tokens lex rest' := by
          rw [htcs, hrest, tokens_punct_cons hp]
        obtain ⟨g', hg'⟩ := realize_complete_aux rest'
        rw [htcs2]
        refine ⟨consGaps (Token.single c hcs) ⟨cs.takeWhile lex.sep, hlead⟩ g'
          (fun _ _ _ => .inr (.inl (by simp [Token.isPunct, hp]))), ?_⟩
        rw [realize_consGaps, hg', Token.single_toList, List.singleton_append, ← hrest]
        exact hsplit
      · -- a word: the maximal run of word characters
        have hcw : lex.word c = true := Lexicon.word_of hcs (by simpa using hp)
        have hwword : ∀ x ∈ (skipSep lex cs).takeWhile lex.word, lex.word x = true :=
          fun x hx => mem_takeWhile hx
        have hwne : (skipSep lex cs).takeWhile lex.word ≠ [] := by
          rw [hrest]; simp [hcw]
        have hw : (skipSep lex cs).takeWhile lex.word ++ afterWord lex (skipSep lex cs)
            = skipSep lex cs := List.takeWhile_append_dropWhile
        have hstop : HeadIn (fun x => lex.word x = false) (afterWord lex (skipSep lex cs)) := by
          intro x hx
          cases haws : afterWord lex (skipSep lex cs) with
          | nil => rw [haws] at hx; simp at hx
          | cons y ys =>
              rw [haws, List.head?_cons, Option.some.injEq] at hx
              subst hx
              exact dropWhile_head_false (p := lex.word) (l := skipSep lex cs)
                (by rw [afterWord] at haws; exact haws)
        have htcs2 : tokens lex cs = Token.ofWord _ hwword hwne ::
            tokens lex (afterWord lex (skipSep lex cs)) := by
          have := tokens_token (Token.ofWord _ hwword hwne) (.inr hstop)
          rw [Token.ofWord_toList, hw] at this
          rw [htcs, this]
        obtain ⟨g', hg'⟩ := realize_complete_aux (afterWord lex (skipSep lex cs))
        rw [htcs2]
        have hok : GapOk (Token.ofWord _ hwword hwne) g'.leading.val
            (tokens lex (afterWord lex (skipSep lex cs))) := by
          intro u us hts
          by_cases hl : g'.leading.val = []
          · -- nothing separates the word from `u`, so `u` begins with what stopped the word
            refine .inr (.inr ?_)
            have hh := realize_head_of_emptyLead g' hl hts
            rw [hg'] at hh
            cases hu : u.val.toList with
            | nil => exact absurd hu u.toList_ne_nil
            | cons x xs =>
                rw [hu, List.head?_cons] at hh
                have hxw : lex.word x = false := hstop x hh
                have hxs : lex.sep x = false := u.no_sep x (by rw [hu]; exact List.mem_cons_self)
                exact Token.isPunct_of_head (by rw [hu]; rfl)
                  (Lexicon.punct_of_not_word hxs hxw)
          · exact .inl hl
        refine ⟨consGaps _ ⟨cs.takeWhile lex.sep, hlead⟩ g' hok, ?_⟩
        rw [realize_consGaps, hg', Token.ofWord_toList, hw]
        exact hsplit
  termination_by cs.length
  decreasing_by
    · have h2 : (skipSep lex cs).length = rest'.length + 1 := by rw [hrest]; simp
      have h3 : (skipSep lex cs).length ≤ cs.length := length_dropWhile_le _ _
      omega
    · have haw : afterWord lex (skipSep lex cs) = rest'.dropWhile lex.word := by
        rw [afterWord, hrest, List.dropWhile_cons, if_pos hcw]
      have h1 : (afterWord lex (skipSep lex cs)).length ≤ rest'.length := by
        rw [haw]; exact length_dropWhile_le _ _
      have h2 : (skipSep lex cs).length = rest'.length + 1 := by rw [hrest]; simp
      have h3 : (skipSep lex cs).length ≤ cs.length := length_dropWhile_le _ _
      omega

/-! ## The tokenizer as a morphism of `Abs` -/

/-- **The tokenizer of a lexicon**, as an abstraction `List Char ⇝ List Token`, whose annotation
over `ts` is exactly the gaps `Gaps lex ts`. Its canonical print spaces the tokens as the lexicon
asks. Tokenizing is total, so `abstract` never fails. -/
def tokenizer (lex : Lexicon) : Abstraction (List Char) (List (Token lex)) (Gaps lex) where
  abstract cs := some (tokens lex cs)
  realize := Gaps.realize
  default := ⟨emptyRun, defaultInner lex _⟩
  abstract_realize := fun ts g => by
    show some (tokens lex (g.leading.val ++ realizeInner lex ts g.inner)) = some ts
    rw [tokens_sep_prepend g.leading.2, tokens_realizeInner ts g.inner]
  -- **The tokenizer forgets only the gaps**: every string is the realization of the gaps read off
  -- it, and the reason `Gaps` is the annotation family: it is the fiber, spelled structurally
  -- rather than tautologically.
  lossless := fun cs ts h => by
    have hts : tokens lex cs = ts := Option.some.inj h
    subst hts
    exact realize_complete_aux cs

end LambdaLab.Abstraction
