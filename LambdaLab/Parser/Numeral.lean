import LambdaLab.Parser.IsoParser.Token

/-!
# Numeral tokens — `?0`, `#12`, … — and their round-trip

A language whose AST holds a `Nat` (a metavariable index, a de Bruijn level, a literal) needs the
surface to *spell* that `Nat`, or the value type cannot round-trip: `Truncation.Mixfix.Rules`
requires `alg_dest`, "destruct a value and rebuild it from its spelling", so every constructor
must be spellable. Spelling a `Nat` means an encode/decode pair that is provably inverse — which
is the one obligation this file discharges once, for everyone.

Two layers:

* **characters** — `natChars`/`charsNat`, decimal, most-significant first, never empty
  (`charsNat_natChars`), on the digit pair `toDigits`/`ofDigits` proved inverse here.
* **tokens** — `natTok pre …`/`natOfTok`, a prefix character followed by those digits, packaged as
  an `IsoParser.Token sep`. Generic in the separator and the prefix, so `?0` (metavariables),
  `#3` (levels) and friends are all instances.

## Why the digits are hand-rolled

This file used `Nat.digits` and `Nat.ofDigits_digits`, and was the last thing below `Stlc` and
`Arith` importing Mathlib. Everything an executable imports is *linked* into it — erasure removes
a proof term, not the module that proved it — so that one import put ~1300 modules into the
binary. There is still no verified decimal round-trip in core (`Nat.repr` and `String.toNat!` are
not proved inverse), so the pair below is defined and proved here: three short inductions, all on
`Nat.mod_add_div`, which is the only arithmetic fact any of it needs.
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
    (intro hc; subst hc; revert h; decide)

/-! ## `Nat` ↔ decimal digits -/

/-- The decimal digits of `n`, **least** significant first. `0` has no digits, which is what makes
`ofDigits` a left inverse without a special case; `natChars` puts the `'0'` back. -/
def toDigits : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) % 10 :: toDigits ((n + 1) / 10)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Read digits back, least significant first. Horner, so it mirrors `toDigits` step for step and
the round-trip below is one `Nat.mod_add_div` per digit. -/
def ofDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * ofDigits ds

/-- **The digit round-trip.** Each step peels `n % 10` and recurses on `n / 10`; putting them back
together is exactly `Nat.mod_add_div`. -/
theorem ofDigits_toDigits : ∀ n : Nat, ofDigits (toDigits n) = n
  | 0 => by rw [toDigits, ofDigits]
  | n + 1 => by
      rw [toDigits, ofDigits, ofDigits_toDigits ((n + 1) / 10)]
      exact Nat.mod_add_div (n + 1) 10
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Digits produced by `toDigits` really are digits — needed to know `digitChar` is injective on
them, and that every character `natChars` emits is a digit character. -/
theorem toDigits_lt_ten : ∀ (n : Nat), ∀ d ∈ toDigits n, d < 10
  | 0 => by intro d hd; rw [toDigits] at hd; cases hd
  | n + 1 => by
      intro d hd
      rw [toDigits] at hd
      cases hd with
      | head => exact Nat.mod_lt _ (by decide)
      | tail _ h => exact toDigits_lt_ten ((n + 1) / 10) d h
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- A non-zero number has at least one digit. -/
theorem toDigits_ne_nil : ∀ {n : Nat}, n ≠ 0 → toDigits n ≠ []
  | 0, h => absurd rfl h
  | _ + 1, _ => by rw [toDigits]; exact List.cons_ne_nil _ _

/-- `charDigit` undoes `digitChar` pointwise on a list of genuine digits. -/
theorem map_charDigit_digitChar : ∀ (ds : List Nat), (∀ d ∈ ds, d < 10) →
    (ds.map digitChar).map charDigit = ds
  | [], _ => rfl
  | d :: ds, h => by
      simp only [List.map_cons]
      rw [(digitChar_spec (h d (List.Mem.head _))).1,
          map_charDigit_digitChar ds (fun x hx => h x (List.Mem.tail _ hx))]

/-! ## `Nat` ↔ digit characters -/

/-- Decimal characters of `n`, most significant first. Never empty (`0` spells `"0"`). -/
def natChars (n : Nat) : List Char :=
  if n = 0 then ['0'] else ((toDigits n).map digitChar).reverse

def charsNat (cs : List Char) : Nat := ofDigits ((cs.map charDigit).reverse)

theorem natChars_spec (n : Nat) :
    natChars n ≠ [] ∧ ∀ c ∈ natChars n, isDigitChar c = true := by
  unfold natChars
  split
  · exact ⟨by simp, by intro c hc; simp at hc; subst hc; decide⟩
  · next h =>
      refine ⟨?_, ?_⟩
      · simp only [ne_eq, List.reverse_eq_nil_iff, List.map_eq_nil_iff]
        exact toDigits_ne_nil h
      · intro c hc
        simp only [List.mem_reverse, List.mem_map] at hc
        obtain ⟨d, hd, rfl⟩ := hc
        exact (digitChar_spec (toDigits_lt_ten n d hd)).2

/-- **The round-trip**: reading back the decimal characters of `n` gives `n`. -/
theorem charsNat_natChars (n : Nat) : charsNat (natChars n) = n := by
  unfold natChars charsNat
  split
  · next h => subst h; decide
  · next h =>
      rw [List.map_reverse, List.reverse_reverse,
        map_charDigit_digitChar _ (toDigits_lt_ten n)]
      exact ofDigits_toDigits n

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
