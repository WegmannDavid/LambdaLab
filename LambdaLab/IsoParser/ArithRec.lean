import LambdaLab.IsoParser.Combinators

/-!
# Recursive grammar via a mutual WF recursion + lexicographic measure — validation

The counterpart to `Arith.lean`, but **recursive** (parentheses), so it exercises the design that
resolves the recursion↔combinators gap:

* the recursion is a plain **mutual well-founded `def`** (not a `fix` combinator), terminating on the
  same **lexicographic measure** CBiparser uses — `(input.length, level)`: descending a precedence
  level (`expr → term`) keeps the input but drops the level; consuming a token (`term → expr` inside
  `( … )`) drops the input length. No recursor is ever wrapped as an `IsoParser`, so nothing partial
  and nothing to make unsound.
* the **leaves** (`digit`, the paren/`+` tokens) are genuine combinator `IsoParser`s (`sat`/`tok`),
  and the round-trip/exactness laws are proved by induction on the same measure, discharging each leaf
  with its combinator lemma and each recursive hole with the induction hypothesis.

Grammar: `expr = term (+ term)*` (left-assoc), `term = digit | ( expr )`.
-/

namespace LambdaLab.IsoParser.ArithRec

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

/-! ## The syntax trees (mutual) -/

mutual
inductive ATerm where
  | digit : Digit → ATerm
  | paren : AExpr → ATerm
  deriving Repr
inductive AExpr where
  | single : ATerm → AExpr
  | add : AExpr → ATerm → AExpr   -- left-nested chain
  deriving Repr
end

/-! ## Flatten (the printer) -/

mutual
def ATerm.flatten : ATerm → List Char
  | .digit c => [c.val]
  | .paren e => '(' :: (e.flatten ++ [')'])
def AExpr.flatten : AExpr → List Char
  | .single t => t.flatten
  | .add e t => e.flatten ++ ('+' :: t.flatten)
end

/-! ## The parser: one mutual WF recursion, lexicographic measure `(length, level)` -/

mutual
  /-- `term = digit | ( expr )`. Level `0`. -/
  def parseTerm (input : List Char) :
      Option (ATerm × { r : List Char // r.length < input.length }) :=
    match hlp : (tok '(').parse input with
    | some (_, r1) =>
      match parseExpr r1.val with
      | some (e, r2) =>
        match (tok ')').parse r2.val with
        | some (_, r3) =>
          some (.paren e, ⟨r3.val, by
            have := r1.property; have := r2.property; have := r3.property; omega⟩)
        | none => none
      | none => none
    | none =>
      match (sat Char.isDigit).parse input with
      | some (d, r1) => some (.digit d.1, r1)
      | none => none
  termination_by (input.length, 0)

  /-- `expr = term (+ term)*`. Level `1`; the seed `parseTerm` is a same-input level drop. -/
  def parseExpr (input : List Char) :
      Option (AExpr × { r : List Char // r.length < input.length }) :=
    match parseTerm input with
    | none => none
    | some (t, s1) =>
      let res := parseAddTail (.single t) s1.val
      some (res.1, ⟨res.2.val, by have := s1.property; have := res.2.property; omega⟩)
  termination_by (input.length, 1)

  /-- Greedy `(+ term)*` fold onto `acc`. Always succeeds; leftover is `≤ input` (zero steps keeps
  the whole input). Level `0`; every recursive call strictly shortens the input. -/
  def parseAddTail (acc : AExpr) (input : List Char) :
      AExpr × { r : List Char // r.length ≤ input.length } :=
    match (tok '+').parse input with
    | some (_, r1) =>
      match parseTerm r1.val with
      | some (t, r2) =>
        let res := parseAddTail (.add acc t) r2.val
        (res.1, ⟨res.2.val, by
          have := r1.property; have := r2.property; have := res.2.property; omega⟩)
      | none => (acc, ⟨input, Nat.le_refl _⟩)
    | none => (acc, ⟨input, Nat.le_refl _⟩)
  termination_by (input.length, 0)
end

/-! ## Compute / round-trip sanity -/

def parse? (s : String) : Option AExpr :=
  match parseExpr s.toList with
  | some (e, ⟨[], _⟩) => some e
  | _ => none

def roundtrip (s : String) : Option String :=
  (parse? s).map (fun e => String.ofList e.flatten)

#eval roundtrip "1+2+3"          -- some "1+2+3"
#eval roundtrip "1+(2+3)"        -- some "1+(2+3)"
#eval roundtrip "((1))"          -- some "((1))"
#eval roundtrip "1+(2+3)+4"      -- some "1+(2+3)+4"
#eval roundtrip "(1+2)+(3+4)"    -- some "(1+2)+(3+4)"
#eval roundtrip "1+"             -- none
#eval roundtrip "(1"             -- none

/-! ## Exactness (`print_parse`): whatever the parser consumed, `flatten` reproduces exactly.

By strong induction on `input.length`. Every recursive call except the `expr → term` seed strictly
shortens the input (so it is covered by the IH); the seed is same-length, handled by proving
`parseTerm` before `parseExpr` inside each length step. The leaves discharge via `tok`/`sat`'s own
`print_parse`. -/

/-- `['(' ] ++ leftover = input` when `tok '('` fires — from `tok`'s exactness. -/
private theorem tok_consumed {t : Char} {input : List Char}
    {x : Σ _ : Unit, PUnit} {r : { r : List Char // r.length < input.length }}
    (h : (tok t).parse input = some (x, r)) : t :: r.val = input := by
  have := (tok t).print_parse input x r h
  simpa [tok] using this

/-- The exactness triple, proved simultaneously by strong induction on the length. -/
theorem exact_all (n : Nat) :
    (∀ input : List Char, input.length = n → ∀ t r,
        parseTerm input = some (t, r) → t.flatten ++ r.val = input) ∧
    (∀ input : List Char, input.length = n → ∀ acc,
        (parseAddTail acc input).1.flatten ++ (parseAddTail acc input).2.val
          = acc.flatten ++ input) ∧
    (∀ input : List Char, input.length = n → ∀ e r,
        parseExpr input = some (e, r) → e.flatten ++ r.val = input) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    -- `term` exactness at length `n`
    have hterm : ∀ input : List Char, input.length = n → ∀ t r,
        parseTerm input = some (t, r) → t.flatten ++ r.val = input := by
      intro input hn t r ht
      rw [parseTerm] at ht
      split at ht
      · next x r1 hopen =>
        split at ht
        · next e r2 he =>
          split at ht
          · next x3 r3 hclose =>
            simp only [Option.some.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, hr⟩ := ht
            have hrv : r.val = r3.val := congrArg Subtype.val hr.symm
            have hopenc := tok_consumed hopen                                   -- '(' :: r1.val = input
            have hexpr := (ih r1.val.length (hn ▸ r1.property)).2.2 r1.val rfl e r2 he
                                                                                -- e.flatten ++ r2.val = r1.val
            have hclosec := tok_consumed hclose                                 -- ')' :: r3.val = r2.val
            simp only [ATerm.flatten]
            rw [hrv]
            calc '(' :: (e.flatten ++ [')']) ++ r3.val
                = '(' :: (e.flatten ++ (')' :: r3.val)) := by simp [List.append_assoc]
              _ = '(' :: (e.flatten ++ r2.val) := by rw [hclosec]
              _ = '(' :: r1.val := by rw [hexpr]
              _ = input := hopenc
          · simp at ht
        · simp at ht
      · next hopen =>
        split at ht
        · next d r1 hd =>
          simp only [Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          have := (sat Char.isDigit).print_parse input d r1 hd
          simpa [sat, ATerm.flatten] using this
        · simp at ht
    -- `addTail` exactness at length `n`
    have haddtail : ∀ input : List Char, input.length = n → ∀ acc,
        (parseAddTail acc input).1.flatten ++ (parseAddTail acc input).2.val
          = acc.flatten ++ input := by
      intro input hn acc
      rw [parseAddTail]
      split
      · next x r1 hplus =>
        split
        · next t r2 ht =>
          have hplusc := tok_consumed hplus                                    -- '+' :: r1.val = input
          have htermc := (ih r1.val.length (by have := r1.property; omega)).1
                            r1.val rfl t r2 ht                                  -- t.flatten ++ r2.val = r1.val
          have hrec := (ih r2.val.length (by have := r1.property; have := r2.property; omega)).2.1
                        r2.val rfl (AExpr.add acc t)
          simp only
          rw [hrec]
          calc (AExpr.add acc t).flatten ++ r2.val
              = acc.flatten ++ ('+' :: (t.flatten ++ r2.val)) := by
                simp [AExpr.flatten, List.append_assoc]
            _ = acc.flatten ++ ('+' :: r1.val) := by rw [htermc]
            _ = acc.flatten ++ input := by rw [hplusc]
        · simp
      · simp
    refine ⟨hterm, haddtail, ?_⟩
    -- `expr` exactness at length `n`, using `term` (same length) + `addTail` (shorter)
    intro input hn e r he
    rw [parseExpr] at he
    split at he
    · simp at he
    · next t s1 hts =>
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, hr⟩ := he
      have hrv : r.val = (parseAddTail (.single t) s1.val).2.val := congrArg Subtype.val hr.symm
      have htermc := hterm input hn t s1 hts                                    -- t.flatten ++ s1.val = input
      have hrec := (ih s1.val.length (by have := s1.property; omega)).2.1
                      s1.val rfl (AExpr.single t)
      rw [hrv]
      calc (parseAddTail (.single t) s1.val).1.flatten ++ (parseAddTail (.single t) s1.val).2.val
          = (AExpr.single t).flatten ++ s1.val := hrec
        _ = t.flatten ++ s1.val := rfl
        _ = input := htermc

end LambdaLab.IsoParser.ArithRec
