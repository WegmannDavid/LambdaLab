import Mathlib.Tactic
import LambdaLab.Abstraction.Basic
import LambdaLab.CBiparser.Tokenizer

/-!
# The tokenizer as a morphism of `Abs` (indexed design)

`List Char ⇝ List Token`. The lossy map is `tokens` (tokenize), which forgets the separators; the
**annotation over a token sequence `ts` is exactly the gaps** — the separator runs that, interleaved
with `ts`, reconstruct a character string tokenizing to `ts`:

```
lead · t₁ · g₁ · t₂ · … · gₙ₋₁ · tₙ · trail
```

`lead`/`trail` may be empty (a string need not start or end with whitespace, and the empty / all-
whitespace strings tokenize to `[]`); the interior gaps `gᵢ` must be **non-empty**, else two tokens
would fuse. Encoding that non-emptiness *in the type* (`NEGap` between tokens, `SepRun` at the ends)
is what makes `abstract_realize` — tokenize the reconstruction and recover `ts` — go through.
-/

namespace LambdaLab.Abstraction

open LambdaLab.CBiparser

variable {sep : Char → Bool}

/-- A possibly-empty run of separators. -/
def SepRun (sep : Char → Bool) : Type := { g : List Char // ∀ c ∈ g, sep c = true }

/-- A non-empty run of separators. -/
def NEGap (sep : Char → Bool) : Type := { g : List Char // g ≠ [] ∧ ∀ c ∈ g, sep c = true }

def NEGap.toSepRun (g : NEGap sep) : SepRun sep := ⟨g.1, g.2.2⟩

theorem head?_append_ne {α : Type} {l : List α} (h : l ≠ []) (l' : List α) :
    (l ++ l').head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- The gaps *after the leading run* for a token list: nothing for `[]`, a trailing run for a single
token, and a non-empty interior gap before each further token. -/
def Inner (sep : Char → Bool) : List (Token sep) → Type
  | []          => PUnit
  | [_]         => SepRun sep
  | _ :: rest   => NEGap sep × Inner sep rest

/-- The annotation over `ts`: a leading run plus the interior/trailing gaps. -/
structure Gaps (sep : Char → Bool) (ts : List (Token sep)) where
  leading : SepRun sep
  inner : Inner sep ts

/-! ## Realization: interleave the tokens with their gaps -/

def realizeInner (sep : Char → Bool) : (ts : List (Token sep)) → Inner sep ts → List Char
  | [],          _  => []
  | [t],         tr => t.val.toList ++ tr.val
  | t :: _ :: _, gi => t.val.toList ++ gi.1.val ++ realizeInner sep _ gi.2

/-- Reconstruct the character string from a token list and its gaps. -/
def Gaps.realize {ts : List (Token sep)} (g : Gaps sep ts) : List Char :=
  g.leading.val ++ realizeInner sep ts g.inner

/-! ## Canonical gaps: one separator `sc` between tokens, empty ends -/

/-- The one-character separator run `[sc]`. -/
def scGap (sc : Char) (hsc : sep sc = true) : NEGap sep :=
  ⟨[sc], by
    refine ⟨by simp, ?_⟩
    intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact hsc⟩

/-- The empty separator run. -/
def emptyRun : SepRun sep := ⟨[], by intro c hc; simp at hc⟩

def defaultInner (sc : Char) (hsc : sep sc = true) :
    (ts : List (Token sep)) → Inner sep ts
  | []           => PUnit.unit
  | [_]          => emptyRun
  | _ :: u :: us => (scGap sc hsc, defaultInner sc hsc (u :: us))

/-! ## `abstract ∘ realize = ts`

Rendering the gaps and re-tokenizing recovers `ts`: the leading run is skipped, and each token is
peeled off because the run following it is a separator (empty trailing, or non-empty interior). -/

theorem tokens_nil : tokens sep [] = [] := by simp [tokens]

theorem tokens_all_sep {g : List Char} (h : ∀ c ∈ g, sep c = true) : tokens sep g = [] := by
  induction g with
  | nil => exact tokens_nil
  | cons c g' ih =>
      rw [tokens_sep_cons (h c List.mem_cons_self)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem headIn_of_allSep {g : List Char} (h : ∀ c ∈ g, sep c = true) : HeadIn sep g := by
  intro a ha
  cases g with
  | nil => simp at ha
  | cons c cs =>
      rw [List.head?_cons] at ha
      simp only [Option.some.injEq] at ha; subst ha
      exact h c List.mem_cons_self

theorem tokens_realizeInner : ∀ (ts : List (Token sep)) (inner : Inner sep ts),
    tokens sep (realizeInner sep ts inner) = ts
  | [],           _  => by rw [show realizeInner sep [] _ = [] from rfl]; exact tokens_nil
  | [t],          tr => by
      rw [show realizeInner sep [t] tr = t.val.toList ++ (tr : SepRun sep).val from rfl,
        tokens_token t (headIn_of_allSep tr.2), tokens_all_sep tr.2]
  | t :: u :: us, gi => by
      have hg : ∀ c ∈ (gi.1 : NEGap sep).val, sep c = true := gi.1.2.2
      have hrw : realizeInner sep (t :: u :: us) gi
          = t.val.toList ++ (gi.1.val ++ realizeInner sep (u :: us) gi.2) := by
        simp [realizeInner, List.append_assoc]
      have hhead : HeadIn sep (gi.1.val ++ realizeInner sep (u :: us) gi.2) := by
        intro a ha
        cases hv : gi.1.val with
        | nil => exact absurd hv gi.1.2.1
        | cons x xs =>
            rw [hv, List.cons_append, List.head?_cons] at ha
            simp only [Option.some.injEq] at ha; subst ha
            exact hg x (by rw [hv]; exact List.mem_cons_self)
      rw [hrw, tokens_token t hhead, tokens_sep_prepend hg, tokens_realizeInner (u :: us) gi.2]

/-! ## `realize` is surjective onto every character string (faithful decomposition)

Every `cs` is the realization of the gaps read off it: the leading separators, then each maximal
token followed by its trailing/interior separators. -/

/-- Prepend a token `t` (with a new leading run) in front of the gaps `g'`. The old leading run of
`g'` becomes the gap after `t` — which must be non-empty when `g'` still has tokens (`hne`). -/
def consInner (t : Token sep) (gap : SepRun sep) :
    (ts : List (Token sep)) → Inner sep ts → (ts ≠ [] → gap.val ≠ []) → Inner sep (t :: ts)
  | [],      _,     _   => gap
  | _ :: _,  inner, hne => (⟨gap.val, hne (by simp), gap.2⟩, inner)

def consGaps (t : Token sep) (newLead : SepRun sep) {ts : List (Token sep)} (g' : Gaps sep ts)
    (hne : ts ≠ [] → g'.leading.val ≠ []) : Gaps sep (t :: ts) :=
  ⟨newLead, consInner t g'.leading ts g'.inner hne⟩

theorem realize_consGaps (t : Token sep) (newLead : SepRun sep) {ts : List (Token sep)}
    (g' : Gaps sep ts) (hne : ts ≠ [] → g'.leading.val ≠ []) :
    Gaps.realize (consGaps t newLead g' hne)
      = newLead.val ++ (t.val.toList ++ Gaps.realize g') := by
  cases ts with
  | nil => simp [Gaps.realize, consGaps, consInner, realizeInner, List.append_assoc]
  | cons v vs => simp [Gaps.realize, consGaps, consInner, realizeInner, List.append_assoc]

theorem realizeInner_head {v : Token sep} {vs : List (Token sep)} (inner : Inner sep (v :: vs)) :
    (realizeInner sep (v :: vs) inner).head? = v.val.toList.head? := by
  cases vs with
  | nil => exact head?_append_ne v.toList_ne_nil _
  | cons v2 vs2 =>
      show (v.val.toList ++ (inner.1.val) ++ realizeInner sep (v2 :: vs2) inner.2).head? = _
      rw [List.append_assoc]; exact head?_append_ne v.toList_ne_nil _

/-- With an empty leading run, a realization of a non-empty token list starts with a *token* char,
which is not a separator. -/
theorem realize_head_of_emptyLead {ts : List (Token sep)} (g : Gaps sep ts)
    (hl : g.leading.val = []) (hne : ts ≠ []) :
    ∃ x, (Gaps.realize g).head? = some x ∧ sep x = false := by
  cases ts with
  | nil => exact absurd rfl hne
  | cons v vs =>
      have hh : (Gaps.realize g).head? = v.val.toList.head? := by
        rw [Gaps.realize, hl, List.nil_append]; exact realizeInner_head g.inner
      cases hvv : v.val.toList with
      | nil => exact absurd hvv v.toList_ne_nil
      | cons z zs =>
          refine ⟨z, ?_, v.no_sep z (by rw [hvv]; exact List.mem_cons_self)⟩
          rw [hh, hvv, List.head?_cons]

theorem realize_complete_aux (cs : List Char) :
    ∃ g : Gaps sep (tokens sep cs), Gaps.realize g = cs := by
  have hlead : ∀ c ∈ cs.takeWhile sep, sep c = true := fun c hc => mem_takeWhile hc
  have hsplit : cs.takeWhile sep ++ skipSep sep cs = cs := List.takeWhile_append_dropWhile
  have htcs : tokens sep cs = tokens sep (skipSep sep cs) := by
    calc tokens sep cs = tokens sep (cs.takeWhile sep ++ skipSep sep cs) := by rw [hsplit]
      _ = tokens sep (skipSep sep cs) := tokens_sep_prepend hlead
  cases hrest : skipSep sep cs with
  | nil =>
      have htk : tokens sep cs = [] := by rw [htcs, hrest]; exact tokens_nil
      rw [htk]
      refine ⟨⟨⟨cs.takeWhile sep, hlead⟩, PUnit.unit⟩, ?_⟩
      show cs.takeWhile sep ++ realizeInner sep [] PUnit.unit = cs
      have hdrop : cs.dropWhile sep = [] := hrest
      simp only [realizeInner, List.append_nil]
      calc cs.takeWhile sep = cs.takeWhile sep ++ cs.dropWhile sep := by rw [hdrop, List.append_nil]
        _ = cs := List.takeWhile_append_dropWhile
  | cons c rest' =>
      have hw : (skipSep sep cs).takeWhile (fun x => !sep x) ++ afterWord sep (skipSep sep cs)
          = skipSep sep cs := List.takeWhile_append_dropWhile
      have hwsep : ∀ x ∈ (skipSep sep cs).takeWhile (fun x => !sep x), sep x = false :=
        fun x hx => by have := mem_takeWhile hx; simpa using this
      have hwne : (skipSep sep cs).takeWhile (fun x => !sep x) ≠ [] := by
        rw [hrest]
        have hcns : sep c = false := by
          have := dropWhile_head_false (p := sep) (l := cs) (a := c) (t := rest')
            (by rw [skipSep] at hrest; exact hrest)
          exact this
        simp only [List.takeWhile_cons, show (fun x => !sep x) c = true from by simp [hcns]]
        simp
      let t : Token sep := Token.ofChars sep _ hwsep hwne
      have htchars : t.val.toList = (skipSep sep cs).takeWhile (fun x => !sep x) :=
        Token.ofChars_toList sep _ hwsep hwne
      have hawhead : HeadIn sep (afterWord sep (skipSep sep cs)) := by
        intro x hx
        cases haws : afterWord sep (skipSep sep cs) with
        | nil => rw [haws] at hx; simp at hx
        | cons y ys =>
            rw [haws, List.head?_cons, Option.some.injEq] at hx
            have hxy : x = y := hx.symm; subst hxy
            have := dropWhile_head_false (p := fun z => !sep z) (l := skipSep sep cs)
              (a := x) (t := ys) (by rw [afterWord] at haws; exact haws)
            simpa using this
      have he : skipSep sep cs = t.val.toList ++ afterWord sep (skipSep sep cs) := by
        rw [htchars]; exact hw.symm
      have htcs2 : tokens sep cs = t :: tokens sep (afterWord sep (skipSep sep cs)) := by
        rw [htcs]; nth_rewrite 1 [he]; exact tokens_token t hawhead
      obtain ⟨g', hg'⟩ := realize_complete_aux (afterWord sep (skipSep sep cs))
      rw [htcs2]
      have hne : tokens sep (afterWord sep (skipSep sep cs)) ≠ [] → g'.leading.val ≠ [] := by
        intro htne hnil
        obtain ⟨x, hxh, hxsep⟩ := realize_head_of_emptyLead g' hnil htne
        rw [hg'] at hxh
        have hseph : sep x = true := by
          cases haws : afterWord sep (skipSep sep cs) with
          | nil => rw [haws] at hxh; simp at hxh
          | cons y ys =>
              rw [haws, List.head?_cons, Option.some.injEq] at hxh
              have hxy : x = y := hxh.symm; subst hxy
              have := dropWhile_head_false (p := fun z => !sep z) (l := skipSep sep cs)
                (a := x) (t := ys) (by rw [afterWord] at haws; exact haws)
              simpa using this
        rw [hxsep] at hseph; exact absurd hseph (by simp)
      refine ⟨consGaps t ⟨cs.takeWhile sep, hlead⟩ g' hne, ?_⟩
      rw [realize_consGaps, hg', htchars, hw]
      exact hsplit
  termination_by cs.length
  decreasing_by
    have hcns : sep c = false := by
      have := dropWhile_head_false (p := sep) (l := cs) (a := c) (t := rest')
        (by rw [skipSep] at hrest; exact hrest)
      exact this
    have haw : afterWord sep (skipSep sep cs) = rest'.dropWhile (fun x => !sep x) := by
      rw [afterWord, hrest, List.dropWhile_cons, if_pos (by simp [hcns])]
    have h1 : (afterWord sep (skipSep sep cs)).length ≤ rest'.length := by
      rw [haw]; exact length_dropWhile_le _ _
    have h2 : (skipSep sep cs).length = rest'.length + 1 := by rw [hrest]; simp
    have h3 : (skipSep sep cs).length ≤ cs.length := length_dropWhile_le _ _
    omega

/-! ## The tokenizer as a morphism of `Abs` -/

/-- The tokenizer for separator predicate `sep`, with witness separator `sc`, as an abstraction
`List Char ⇝ List Token`, whose annotation over `ts` is exactly the gaps `Gaps sep ts`. -/
def tokenizer (sc : Char) (hsc : sep sc = true) :
    Abstraction (List Char) (List (Token sep)) (Gaps sep) where
  abstract := tokens sep
  realize := Gaps.realize
  default := ⟨emptyRun, defaultInner sc hsc _⟩
  abstract_realize := fun ts g => by
    show tokens sep (g.leading.val ++ realizeInner sep ts g.inner) = ts
    rw [tokens_sep_prepend g.leading.2, tokens_realizeInner ts g.inner]
  realize_complete := fun cs => realize_complete_aux cs

end LambdaLab.Abstraction
