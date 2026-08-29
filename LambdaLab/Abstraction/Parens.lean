import Mathlib.Tactic
import LambdaLab.Abstraction.Tokenizer

/-!
# Redundant parentheses — the first *lossy* parser stage

The pipeline's `parse` stage: a parser that accepts `((((a))))`, abstracts it to just `a`, and
canonically prints it back as `a`. The forgotten information — how many redundant parens the
source wrote — goes in the annotation, which is what lets the stage keep the `complete` law.

## Design: a combinator on `Abs` morphisms, not a lossy `IsoParser`

`IsoParser`'s type *bundles* the no-loss law; weakening it would forfeit what it is for. Instead,
lossy parsing lives at the `Abstraction` level, built compositionally:

* `atom` — the smallest parser: exactly one token satisfying a predicate. `Unit` annotation:
  a lossless partial iso (the `Unit ⟺ lossless` slogan).
* `Abstraction.parens` — a **combinator**: wrap *any* stage `p` in arbitrarily many redundant
  parens. Annotation `Nat × Ann v` — the nesting depth, then `p`'s own annotation. `default`
  is `(0, p.default)`: the canonical print has **no** redundant parens.

`parens` needs two side conditions: `lp ≠ rp` (so `strip` and `wrap` round-trip), and `hp` — no
realization of `p` may itself begin with `lp` *and* end with `rp`, else the stripper would eat
one pair too many. For `atom` the latter is free from the former (a single token cannot be both).
`complete` is inherited: the combinator's proof consumes `p.complete`.

Scope: this wraps the *whole* input in parens (a toy grammar), not parens at every node
of a recursive grammar — that generalization is the mixfix-as-`Abs` port, later.

The bottom of the file composes `tokenizer ⋙ parens atom` into the first two-stage pipeline
`List Char ⇝ {var}` — complete by construction, since every stage now is.
-/

namespace LambdaLab.Abstraction

variable {Tok V : Type} {Ann : V → Type}

/-! ## The atomic stage: one token -/

/-- Exactly one token satisfying `isVar`. `Unit` annotation — nothing is forgotten. -/
def atom (isVar : Tok → Bool) :
    Abstraction (List Tok) { t : Tok // isVar t = true } (fun _ => Unit) where
  abstract := fun cs =>
    match cs with
    | [t] => if h : isVar t = true then some ⟨t, h⟩ else none
    | _ => none
  realize {v} _ := [v.1]
  default := ()
  abstract_realize v _ := by simp; exact v.2
  complete cs v h := by
    match cs with
    | [] => have h' : (none : Option _) = some v := h; simp at h'
    | [t] =>
        refine ⟨(), ?_⟩
        show [v.1] = [t]
        have h' : (if h : isVar t = true then some ⟨t, h⟩ else none) = some v := h
        split at h'
        · cases h'; rfl
        · simp at h'
    | _ :: _ :: _ => have h' : (none : Option _) = some v := h; simp at h'

/-! ## Stripping and wrapping parens -/

/-- Peel matched outer `lp`/`rp` pairs: the nesting depth and the core. -/
def strip [DecidableEq Tok] (lp rp : Tok) (cs : List Tok) : Nat × List Tok :=
  if h : cs.head? = some lp ∧ cs.getLast? = some rp then
    let r := strip lp rp cs.tail.dropLast
    (r.1 + 1, r.2)
  else (0, cs)
  termination_by cs.length
  decreasing_by
    cases cs with
    | nil => simp at h
    | cons a as => simp [List.length_dropLast]

/-- Wrap in `n` pairs of parens. -/
def wrap (lp rp : Tok) : Nat → List Tok → List Tok
  | 0, w => w
  | n + 1, w => lp :: (wrap lp rp n w ++ [rp])

/-- Stripping a wrap recovers the depth and the core — provided the core does not itself look
wrapped (begin with `lp` *and* end with `rp`). -/
theorem strip_wrap [DecidableEq Tok] {lp rp : Tok} {w : List Tok}
    (hw : ¬(w.head? = some lp ∧ w.getLast? = some rp)) :
    ∀ n, strip lp rp (wrap lp rp n w) = (n, w)
  | 0 => by rw [wrap, strip, dif_neg hw]
  | n + 1 => by
      have hlast : (lp :: (wrap lp rp n w ++ [rp])).getLast? = some rp := by
        rw [← List.cons_append]; exact List.getLast?_concat
      rw [wrap, strip, dif_pos ⟨List.head?_cons, hlast⟩]
      simp only [List.tail_cons, List.dropLast_concat]
      rw [strip_wrap hw n]

/-- `strip` is a genuine decomposition: wrapping the core back to the measured depth restores the
input. Needs `lp ≠ rp` (else the singleton `[lp]` "strips" without having a matched pair). -/
theorem strip_sound [DecidableEq Tok] {lp rp : Tok} (hlprp : lp ≠ rp) (cs : List Tok) :
    wrap lp rp (strip lp rp cs).1 (strip lp rp cs).2 = cs := by
  by_cases h : cs.head? = some lp ∧ cs.getLast? = some rp
  · have ih := strip_sound hlprp cs.tail.dropLast
    rw [strip, dif_pos h]
    show wrap lp rp ((strip lp rp cs.tail.dropLast).1 + 1)
        (strip lp rp cs.tail.dropLast).2 = cs
    rw [wrap, ih]
    obtain ⟨h1, h2⟩ := h
    cases cs with
    | nil => simp at h1
    | cons a as =>
        rw [List.head?_cons, Option.some.injEq] at h1
        subst h1
        simp only [List.tail_cons]
        rcases List.eq_nil_or_concat as with rfl | ⟨as', x, rfl⟩
        · simp at h2
          exact absurd h2 hlprp
        · simp only [List.concat_eq_append] at h2 ⊢
          rw [show a :: (as' ++ [x]) = (a :: as') ++ [x] from rfl,
            List.getLast?_concat, Option.some.injEq] at h2
          subst h2
          simp
  · rw [strip, dif_neg h]; rfl
  termination_by cs.length
  decreasing_by
    cases cs with
    | nil => simp at h
    | cons a as => simp [List.length_dropLast]

/-! ## The combinator -/

/-- Wrap a stage in arbitrarily many redundant parens. The annotation grows by the nesting depth;
the canonical print (`default`) uses none. `hp`: no realization of `p` may look wrapped itself,
else stripping would eat into it. -/
def _root_.LambdaLab.Abstraction.parens [DecidableEq Tok] (p : Abstraction (List Tok) V Ann) (lp rp : Tok)
    (hlprp : lp ≠ rp)
    (hp : ∀ (v : V) (ann : Ann v),
      ¬((p.realize ann).head? = some lp ∧ (p.realize ann).getLast? = some rp)) :
    Abstraction (List Tok) V (fun v => Nat × Ann v) where
  abstract cs := p.abstract (strip lp rp cs).2
  realize x := wrap lp rp x.1 (p.realize x.2)
  default := (0, p.default)
  abstract_realize v x := by
    show p.abstract (strip lp rp (wrap lp rp x.1 (p.realize x.2))).2 = some v
    rw [strip_wrap (hp v x.2)]
    exact p.abstract_realize v x.2
  complete cs v h := by
    obtain ⟨ann, hann⟩ := p.complete _ v h
    refine ⟨((strip lp rp cs).1, ann), ?_⟩
    show wrap lp rp (strip lp rp cs).1 (p.realize ann) = cs
    rw [hann]
    exact strip_sound hlprp cs

/-- For `atom`, the `parens` side condition is free: a single-token realization would need
`lp = rp` to look wrapped. -/
theorem atom_neverWrapped {isVar : Tok → Bool} {lp rp : Tok} (hlprp : lp ≠ rp) :
    ∀ (v : { t : Tok // isVar t = true }) (ann : Unit),
      ¬(((atom isVar).realize (a := v) ann).head? = some lp
        ∧ ((atom isVar).realize (a := v) ann).getLast? = some rp) := by
  rintro v ann ⟨h1, h2⟩
  simp only [atom] at h1 h2
  rw [List.head?_cons, Option.some.injEq] at h1
  rw [List.getLast?_singleton, Option.some.injEq] at h2
  exact hlprp (h1.symm.trans h2)

/-! ## The motivating example, end to end: `((((a)))) ↦ a`

Compose the tokenizer with the parens-wrapped atom: the first two-stage pipeline. Its composite
annotation is `Σ (depth, ()), Gaps` — everything the source wrote that the abstract value forgot:
the redundant parens and the whitespace. -/

section Demo

def sepSp (c : Char) : Bool := c == ' '

private def lpT : Parser.IsoParser.Token sepSp := ⟨"(", by decide⟩
private def rpT : Parser.IsoParser.Token sepSp := ⟨")", by decide⟩

private def isVarT (t : Parser.IsoParser.Token sepSp) : Bool := decide (t ≠ lpT) && decide (t ≠ rpT)

private theorem lp_ne_rp : lpT ≠ rpT := by decide

/-- `List Char ⇝ {var}`: tokenize, then strip redundant parens around a variable. -/
def parenVarPipeline :
    Abstraction (List Char) { t : Parser.IsoParser.Token sepSp // isVarT t = true }
      (fun v => Σ x : Nat × Unit, Gaps sepSp (wrap lpT rpT x.1 [v.1])) :=
  (tokenizer ' ' rfl).comp ((atom isVarT).parens lpT rpT lp_ne_rp (atom_neverWrapped lp_ne_rp))

end Demo

end LambdaLab.Abstraction
