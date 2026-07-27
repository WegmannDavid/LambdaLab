import LambdaLab.Parser.IsoParser.Token
import Mathlib.Data.Nat.Digits.Defs

/-!
# Numeral tokens — `?0`, `#12`, … — and their round-trip

A language whose AST holds a `Nat` (a metavariable index, a de Bruijn level, a literal) needs the
surface to *spell* that `Nat`, or the value type cannot round-trip: `Truncation.Mixfix.Rules`
requires `alg_dest`, "destruct a value and rebuild it from its spelling", so every constructor
must be spellable. Spelling a `Nat` means an encode/decode pair that is provably inverse — which
is the one obligation this file discharges once, for everyone.

Two layers:

* **characters** — `natChars`/`charsNat`, decimal, most-significant first, never empty
  (`charsNat_natChars`). Built on Mathlib's `Nat.ofDigits_digits`; there is no
  `(toString n).toNat! = n` in core or Mathlib to lean on.
* **tokens** — `natTok pre …`/`natOfTok`, a prefix character followed by those digits, packaged as
  an `IsoParser.Token sep`. Generic in the separator and the prefix, so `?0` (metavariables),
  `#3` (levels) and friends are all instances.

⚠ This is the one file in `Parser/` that imports Mathlib. It is a leaf — nothing in the parser
core imports it — so the core stays Mathlib-free; only a language that wants numeral tokens pays.
-/

namespace LambdaLab.Parser.Numeral

open LambdaLab.Parser.IsoParser

/-! ## Digit characters -/

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)
def charDigit (c : Char) : Nat := c.toNat - 48
def isDigitChar (c : Char) : Bool := decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)

/-- Everything needed about a decimal digit's character, by exhaustion over the ten digits. -/
theorem digitChar_spec : ∀ {d : Nat}, d < 10 →
    charDigit (digitChar d) = d ∧ isDigitChar (digitChar d) = true
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide

/-- Digits are not whitespace — the common instance of the separator side-condition below. -/
theorem isDigitChar_not_whitespace {c : Char} (h : isDigitChar c = true) :
    c.isWhitespace = false := by
  simp only [isDigitChar, decide_eq_true_eq] at h
  simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
    (rintro rfl; revert h; decide)

/-! ## `Nat` ↔ digit characters -/

/-- Decimal characters of `n`, most significant first. Never empty (`0` spells `"0"`). -/
def natChars (n : Nat) : List Char :=
  if n = 0 then ['0'] else ((Nat.digits 10 n).map digitChar).reverse

def charsNat (cs : List Char) : Nat := Nat.ofDigits 10 ((cs.map charDigit).reverse)

theorem natChars_spec (n : Nat) :
    natChars n ≠ [] ∧ ∀ c ∈ natChars n, isDigitChar c = true := by
  unfold natChars
  split
  · exact ⟨by simp, by intro c hc; simp at hc; subst hc; decide⟩
  · next h =>
      refine ⟨?_, ?_⟩
      · simp only [ne_eq, List.reverse_eq_nil_iff, List.map_eq_nil_iff]
        exact Nat.digits_ne_nil_iff_ne_zero.mpr h
      · intro c hc
        simp only [List.mem_reverse, List.mem_map] at hc
        obtain ⟨d, hd, rfl⟩ := hc
        exact (digitChar_spec (Nat.digits_lt_base (by norm_num) hd)).2

/-- **The round-trip**: reading back the decimal characters of `n` gives `n`. -/
theorem charsNat_natChars (n : Nat) : charsNat (natChars n) = n := by
  unfold natChars charsNat
  split
  · next h => subst h; decide
  · next h =>
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      have hid : ∀ d ∈ Nat.digits 10 n, (charDigit ∘ digitChar) d = id d :=
        fun d hd => (digitChar_spec (Nat.digits_lt_base (by norm_num) hd)).1
      rw [List.map_congr_left hid, List.map_id]
      exact Nat.ofDigits_digits 10 n

/-! ## Numeral tokens -/

variable {sep : Char → Bool}

/-- Is `t` the prefix character `pre` followed by at least one decimal digit? -/
def isNatTok (pre : Char) (t : Token sep) : Bool :=
  match t.val.toList with
  | c :: ds => c == pre && !ds.isEmpty && ds.all isDigitChar
  | _ => false

/-- The token spelling `pre` followed by `n` in decimal. The side conditions say the prefix and
the digits are not separators — otherwise the "token" would re-lex as several. -/
def natTok (pre : Char) (hpre : sep pre = false)
    (hdig : ∀ c, isDigitChar c = true → sep c = false) (n : Nat) : Token sep :=
  ⟨String.ofList (pre :: natChars n), isToken_iff.mpr (by
    rw [String.toList_ofList]
    refine ⟨?_, by simp⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hpre
    · exact hdig c ((natChars_spec n).2 c hc'))⟩

/-- Read the number back out (the prefix is dropped). -/
def natOfTok (t : Token sep) : Nat := charsNat t.val.toList.tail

theorem natOfTok_natTok (pre : Char) (hpre : sep pre = false)
    (hdig : ∀ c, isDigitChar c = true → sep c = false) (n : Nat) :
    natOfTok (natTok pre hpre hdig n) = n := by
  simp only [natOfTok, natTok, String.toList_ofList, List.tail_cons]
  exact charsNat_natChars n

theorem isNatTok_natTok (pre : Char) (hpre : sep pre = false)
    (hdig : ∀ c, isDigitChar c = true → sep c = false) (n : Nat) :
    isNatTok pre (natTok pre hpre hdig n) = true := by
  have hs := natChars_spec n
  simp only [isNatTok, natTok, String.toList_ofList]
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, beq_self_eq_true, true_and]
  refine ⟨?_, fun c hc => hs.2 c hc⟩
  cases hh : natChars n with
  | nil => exact absurd hh hs.1
  | cons a as => simp

end LambdaLab.Parser.Numeral
