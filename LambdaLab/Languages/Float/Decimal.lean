import LambdaLab.Parser.Numeral
import LambdaLab.Pipeline.Basic

/-!
# Exact decimals, and the literals that spell them

The `float` language computes with numbers like `2.5`, and its evaluator writes each result back
into the program as a literal. That is only well-defined if printing a value and reading the
literal back gives the same value — the evaluation walk's idempotence rests on it. So the values are
**exact decimals**, not Lean's `Float`: nothing can be proved about `Float` (its operations are
opaque), and with only `+` and `*` exactness costs nothing, because decimals are closed under both.

A `Decimal` is an integer part and the digits after the point. Both directions of the literal
encoding are by hand, on `Parser/Numeral.lean`'s proved `Nat` round trip:

    I          ↔  ⟨I, []⟩
    I.d₁…dₖ    ↔  ⟨I, [d₁, …, dₖ]⟩

and `decimalOfChars_decimalChars` is the round trip. Values computed by the language are
**normalized** — no trailing zeros after the point — so `0.5 + 0.5` is written `1`, not `1.0`.
Arithmetic itself needs no proof: nothing downstream depends on what `2 + 3` is, only on the fact
that whatever it is, it is written as a literal that reads back as itself.
-/

namespace LambdaLab.Languages.Float

open LambdaLab.Parser.IsoParser (isToken_iff)
open LambdaLab.Parser.Numeral
open LambdaLab.Pipeline (Token)

/-- A non-negative decimal: an integer part, and the digits after the point, most significant
first. -/
structure Decimal where
  int : Nat
  frac : List (Fin 10)
  deriving DecidableEq, Repr

namespace Decimal

/-! ## Arithmetic -/

/-- The fractional digits, read as a number (`[0, 5]` is `5`). -/
def fracNat (f : List (Fin 10)) : Nat := f.foldl (fun acc x => acc * 10 + x.val) 0

/-- As a mantissa and a scale, `m / 10 ^ s`. -/
def toMS (d : Decimal) : Nat × Nat :=
  (d.int * 10 ^ d.frac.length + fracNat d.frac, d.frac.length)

/-- Drop trailing zeros after the point. -/
def stripZeros (f : List (Fin 10)) : List (Fin 10) := (f.reverse.dropWhile (· == 0)).reverse

/-- The canonical form: no trailing zeros after the point. -/
def normalize (d : Decimal) : Decimal := ⟨d.int, stripZeros d.frac⟩

/-- From a mantissa and a scale, normalized. -/
def ofMS (m s : Nat) : Decimal :=
  normalize ⟨m / 10 ^ s,
    (List.range s).reverse.map (fun k => ⟨(m / 10 ^ k) % 10, Nat.mod_lt _ (by decide)⟩)⟩

def add (a b : Decimal) : Decimal :=
  let s := max a.toMS.2 b.toMS.2
  ofMS (a.toMS.1 * 10 ^ (s - a.toMS.2) + b.toMS.1 * 10 ^ (s - b.toMS.2)) s

def mul (a b : Decimal) : Decimal :=
  ofMS (a.toMS.1 * b.toMS.1) (a.toMS.2 + b.toMS.2)

theorem dropWhile_idem {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).dropWhile p = l.dropWhile p
  | [] => rfl
  | a :: l => by
      by_cases h : p a = true
      · simp only [List.dropWhile_cons, h, if_true]; exact dropWhile_idem p l
      · simp [h]

/-- Normalizing twice is normalizing once. -/
theorem normalize_normalize (d : Decimal) : d.normalize.normalize = d.normalize := by
  simp only [normalize, stripZeros, List.reverse_reverse, dropWhile_idem]

theorem ofMS_normalize (m s : Nat) : (ofMS m s).normalize = ofMS m s :=
  normalize_normalize _

/-- Sums come out normalized… -/
theorem add_normalize (a b : Decimal) : (a.add b).normalize = a.add b := ofMS_normalize _ _

/-- …and so do products. -/
theorem mul_normalize (a b : Decimal) : (a.mul b).normalize = a.mul b := ofMS_normalize _ _

/-! ## Literals -/

/-- Split off the leading run of digits. -/
def spanDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if isDigitChar c then ((c :: (spanDigits cs).1), (spanDigits cs).2) else ([], c :: cs)

theorem spanDigits_append : ∀ (ds rest : List Char), (∀ c ∈ ds, isDigitChar c = true) →
    (∀ c, rest.head? = some c → isDigitChar c = false) → spanDigits (ds ++ rest) = (ds, rest)
  | [], [], _, _ => rfl
  | [], c :: cs, _, hr => by
      simp only [List.nil_append, spanDigits, hr c rfl, Bool.false_eq_true, if_false]
  | c :: ds, rest, hd, hr => by
      have ih := spanDigits_append ds rest (fun x hx => hd x (List.mem_cons_of_mem _ hx)) hr
      simp only [List.cons_append, spanDigits, hd c List.mem_cons_self, if_true, ih]

/-- A digit character as a `Fin 10`. -/
def digitOfChar (c : Char) : Fin 10 := ⟨charDigit c % 10, Nat.mod_lt _ (by decide)⟩

theorem digitOfChar_digitChar (x : Fin 10) : digitOfChar (digitChar x.val) = x := by
  apply Fin.ext
  simp only [digitOfChar, (digitChar_spec x.isLt).1, Nat.mod_eq_of_lt x.isLt]

/-- The characters after the integer part: nothing, or a point and the digits. -/
def fracChars : List (Fin 10) → List Char
  | [] => []
  | x :: xs => '.' :: (x :: xs).map (fun d => digitChar d.val)

/-- **The spelling of a decimal**: `I` or `I.d₁…dₖ`. -/
def decimalChars (d : Decimal) : List Char := natChars d.int ++ fracChars d.frac

/-- Read a spelling back. -/
def decimalOfChars (cs : List Char) : Decimal :=
  ⟨charsNat (spanDigits cs).1,
    match (spanDigits cs).2 with
    | c :: f => if c = '.' then f.map digitOfChar else []
    | [] => []⟩

/-- Is this a decimal's spelling — digits, then optionally a point and at least one digit? -/
def isDecimalChars (cs : List Char) : Bool :=
  !(spanDigits cs).1.isEmpty &&
    match (spanDigits cs).2 with
    | [] => true
    | c :: f => c == '.' && !f.isEmpty && f.all isDigitChar

theorem fracChars_head (f : List (Fin 10)) :
    ∀ c, (fracChars f).head? = some c → isDigitChar c = false := by
  intro c hc
  cases f with
  | nil => simp [fracChars] at hc
  | cons x xs =>
      simp only [fracChars, List.head?_cons, Option.some.injEq] at hc
      subst hc; decide

theorem spanDigits_decimalChars (d : Decimal) :
    spanDigits (decimalChars d) = (natChars d.int, fracChars d.frac) :=
  spanDigits_append _ _ (natChars_spec d.int).2 (fracChars_head d.frac)

/-- **The round trip**: reading a decimal's spelling back gives the decimal. -/
theorem decimalOfChars_decimalChars (d : Decimal) : decimalOfChars (decimalChars d) = d := by
  obtain ⟨I, f⟩ := d
  simp only [decimalOfChars, spanDigits_decimalChars, charsNat_natChars]
  cases f with
  | nil => rfl
  | cons x xs =>
      simp only [fracChars, if_true, List.map_map, Function.comp_def, digitOfChar_digitChar,
        List.map_id']

theorem isDecimalChars_decimalChars (d : Decimal) : isDecimalChars (decimalChars d) = true := by
  obtain ⟨I, f⟩ := d
  have hne : (natChars I).isEmpty = false := by
    cases h : natChars I with
    | nil => exact absurd h (natChars_spec I).1
    | cons _ _ => rfl
  simp only [isDecimalChars, spanDigits_decimalChars, hne, Bool.not_false, Bool.true_and]
  cases f with
  | nil => rfl
  | cons x xs =>
      simp only [fracChars, beq_self_eq_true, Bool.true_and]
      rw [Bool.and_eq_true]
      refine ⟨by simp, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hc
      exact (digitChar_spec y.isLt).2

/-! ## Literal tokens -/

/-- Is this token a decimal literal? -/
def isDecimalTok (t : Token) : Bool := isDecimalChars t.val.toList

theorem decimalChars_not_sep (d : Decimal) : ∀ c ∈ decimalChars d, c.isWhitespace = false := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact isDigitChar_not_whitespace ((natChars_spec d.int).2 c h)
  · cases hf : d.frac with
    | nil => rw [hf] at h; cases h
    | cons x xs =>
        rw [hf] at h
        simp only [fracChars, List.mem_cons, List.mem_map] at h
        rcases h with rfl | ⟨y, _, rfl⟩
        · decide
        · exact isDigitChar_not_whitespace (digitChar_spec y.isLt).2

/-- **A decimal's literal token.** -/
def toToken (d : Decimal) : Token :=
  ⟨String.ofList (decimalChars d), isToken_iff.mpr (by
    rw [String.toList_ofList]
    refine ⟨decimalChars_not_sep d, ?_⟩
    intro h
    have := (natChars_spec d.int).1
    simp only [decimalChars, List.append_eq_nil_iff] at h
    exact this h.1)⟩

theorem isDecimalTok_toToken (d : Decimal) : isDecimalTok (toToken d) = true := by
  simp only [isDecimalTok, toToken, String.toList_ofList]
  exact isDecimalChars_decimalChars d

/-- The value a literal token spells, normalized. -/
def ofToken (t : Token) : Decimal := (decimalOfChars t.val.toList).normalize

/-- Reading a value's literal gives the value back, normalized. -/
theorem ofToken_toToken (d : Decimal) : ofToken (toToken d) = d.normalize := by
  simp only [ofToken, toToken, String.toList_ofList, decimalOfChars_decimalChars]

end Decimal

end LambdaLab.Languages.Float
