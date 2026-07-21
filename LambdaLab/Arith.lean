import LambdaLab.Language1.Biparser
import LambdaLab.IsoParser.Mixfix.Biparser
import LambdaLab.IsoParser.Adapters

/-!
# Arithmetic — the running example, end to end

One file, three layers of the same toy language, each exercising a different part of the
`IsoParser` stack. They were previously scattered across `IsoParser/Arith.lean`,
`IsoParser/ArithRec.lean` and `Language1/Arith.lean`.

* `Combinator` — `number (+ number)*`, and a two-level precedence variant. Built *purely* from
  `sat`/`tok`/`many1`/`gdo`/`chainl`, with no recursion, so the round-trip law comes entirely from
  the combinators: zero sorries, nothing to prove by hand.
* `Recursive` — the same grammar plus parentheses, so it needs real recursion. A mutual
  well-founded `def` on the lexicographic measure `(input.length, level)`, with both laws
  (`exact_all`, `parseExpr_print`) proved by hand. Zero sorries.
* the language itself — the mixfix arithmetic vernacular as a `Language1.Language`, plugged into
  the verified mixfix parser. **Its round-trip law is conditional** (see the section note).

The older `ParserOld`/`CBiparser` arithmetic fixtures are deliberately *not* here: they are the
test fixtures for proof files in their own stacks and live next to them.
-/

namespace LambdaLab.Arith

/-! ## Combinator-only grammar

`number (+ number)*`, left-associative, built purely from `sat`/`tok`/`many1`/`gdo`/`chainl`. No
recursion (no parens), so the round-trip law comes **entirely from the combinators** — zero
sorries. Both parsers are **aligned** (source type = value type), so a parsed value can be
re-printed directly and `#eval` confirms the round-trip.
-/

namespace Combinator

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

/-- One or more digits. -/
def number := many1 (sat Char.isDigit) (fun _ _ => trivial)

/-- `+ number`. -/
def addStep : IsoParser Char (· = '+') (fun c => True ∧ ¬ c.isDigit = true)
    (NEList Digit) (NEList Digit) := gdo
  let _p ← tok '+'
  let n ← number
  return n

/-- `number (+ number)*`, left-associative (structural value: seed × steps). -/
def expr := chainl number addStep
  (by intro c hc; subst hc; exact ⟨trivial, by decide⟩)

/-- Round-trip a fully-consumed string through the parsed value (aligned, so it re-prints). -/
def roundtrip (s : String) : Option String :=
  match expr.run s.toList with
  | some (v, []) => some (String.ofList (expr.print v).2)
  | _ => none

#eval roundtrip "1+2+3"     -- some "1+2+3"
#eval roundtrip "42"        -- some "42"
#eval roundtrip "7+80+900"  -- some "7+80+900"
#eval roundtrip "1++2"      -- none  (malformed)
#eval roundtrip "+1"        -- none

/-! ### With precedence — `expr = term (+ term)*`, `term = number (* number)*` -/

/-- `* number`. -/
def mulStep : IsoParser Char (· = '*') (fun c => True ∧ ¬ c.isDigit = true)
    (NEList Digit) (NEList Digit) := gdo
  let _p ← tok '*'
  let n ← number
  return n

/-- `number (* number)*`. -/
def term := chainl number mulStep
  (by intro c hc; subst hc; exact ⟨trivial, by decide⟩)

/-- `+ term`. -/
def addStepT : IsoParser Char (· = '+')
    (fun c => (True ∧ ¬ c.isDigit = true) ∧ ¬ c = '*')
    (NEList Digit × List (NEList Digit)) (NEList Digit × List (NEList Digit)) := gdo
  let _p ← tok '+'
  let t ← term
  return t

/-- `term (+ term)*` — full two-level precedence grammar. -/
def exprPrec := chainl term addStepT
  (by intro c hc; subst hc; exact ⟨⟨trivial, by decide⟩, by decide⟩)

def roundtripP (s : String) : Option String :=
  match exprPrec.run s.toList with
  | some (v, []) => some (String.ofList (exprPrec.print v).2)
  | _ => none

#eval roundtripP "1+2*3"        -- some "1+2*3"  (parses as 1+(2*3), prints back)
#eval roundtripP "2*3+4"        -- some "2*3+4"
#eval roundtripP "1*2*3"        -- some "1*2*3"
#eval roundtripP "10*20+30*40"  -- some "10*20+30*40"

end Combinator

/-! ## Recursive grammar via a mutual WF recursion + lexicographic measure

The counterpart to `Combinator`, but **recursive** (parentheses), so it exercises the design that
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

namespace Recursive

open LambdaLab.IsoParser

abbrev Digit := { c : Char // c.isDigit = true }

/-! ### The syntax trees (mutual) -/

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

/-! ### Flatten (the printer) -/

mutual
def ATerm.flatten : ATerm → List Char
  | .digit c => [c.val]
  | .paren e => '(' :: (e.flatten ++ [')'])
def AExpr.flatten : AExpr → List Char
  | .single t => t.flatten
  | .add e t => e.flatten ++ ('+' :: t.flatten)
end

/-! ### The parser: one mutual WF recursion, lexicographic measure `(length, level)` -/

mutual
  /-- `term = digit | ( expr )`. Level `0`. -/
  def parseTerm (input : List Char) :
      Option (ATerm × { r : List Char // r.length < input.length }) :=
    match hlp : tokParse '(' input with
    | some (_, r1) =>
      match parseExpr r1.val with
      | some (e, r2) =>
        match tokParse ')' r2.val with
        | some (_, r3) =>
          some (.paren e, ⟨r3.val, by
            have := r1.property; have := r2.property; have := r3.property; omega⟩)
        | none => none
      | none => none
    | none =>
      match satParse Char.isDigit input with
      | some (d, r1) => some (.digit d, r1)
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
    match tokParse '+' input with
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

/-! ### Compute / round-trip sanity -/

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

/-! ### Exactness (`print_parse`): whatever the parser consumed, `flatten` reproduces exactly.

By strong induction on `input.length`. Every recursive call except the `expr → term` seed strictly
shortens the input (so it is covered by the IH); the seed is same-length, handled by proving
`parseTerm` before `parseExpr` inside each length step. The leaves discharge via `tok`/`sat`'s own
`print_parse`. -/

/-- `['(' ] ++ leftover = input` when `tokParse '('` fires — leaf exactness, proved directly (the
split model has no `print_parse` field to inherit it from). -/
private theorem tok_consumed {t : Char} {input : List Char}
    {x : Unit} {r : { r : List Char // r.length < input.length }}
    (h : tokParse t input = some (x, r)) : t :: r.val = input := by
  cases input with
  | nil => simp [tokParse] at h
  | cons hd tl =>
    simp only [tokParse] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      subst hp; rfl
    · simp at h

/-- The digit leaf's exactness, proved directly. -/
private theorem sat_consumed {pred : Char → Bool} {input : List Char}
    {d : { c : Char // pred c = true }} {r : { r : List Char // r.length < input.length }}
    (h : satParse pred input = some (d, r)) : d.val :: r.val = input := by
  cases input with
  | nil => simp [satParse] at h
  | cons hd tl =>
    simp only [satParse] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp at h

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
          simpa [ATerm.flatten] using sat_consumed hd
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

/-! ### Round-trip (`parse_print`): print a tree, parse it back, recover it.

The hard direction — the greedy left-associative reconstruction (the analogue of CBiparser's open
`parseExpr_exact`). Structural induction on `AExpr` fails on `add e t`: after parsing `e`, the input
continues with `+`, so `e` is never parsed as a standalone sub-expression. The fix is the **spine** —
every `AExpr` is a seed term left-folded over its `+`-chained steps, and the greedy fold rebuilds it. -/

/-! #### Leaf parse reductions (raw results, no subtype plumbing) -/

private theorem tok_parse_hit (c : Char) (rest : List Char) :
    tokParse c (c :: rest) = some ((), ⟨rest, by simp⟩) := by
  simp [tokParse]

private theorem tok_parse_miss {t c : Char} (rest : List Char) (h : c ≠ t) :
    tokParse t (c :: rest) = none := by simp [tokParse, h]

private theorem sat_parse_hit {pred : Char → Bool} {c : Char} (hc : pred c = true) (rest : List Char) :
    satParse pred (c :: rest) = some (⟨c, hc⟩, ⟨rest, by simp⟩) := by
  simp [satParse, hc]

/-- Extract the raw parse result (with its progress subtype) from the projected `.map` form. -/
private theorem map_proj_eq_some {V : Type} {input : List Char}
    {o : Option (V × { r : List Char // r.length < input.length })} {x : V} {rest : List Char}
    (h : o.map (fun z => (z.1, z.2.val)) = some (x, rest)) :
    ∃ r : { r : List Char // r.length < input.length }, o = some (x, r) ∧ r.val = rest := by
  cases o with
  | none => simp at h
  | some z =>
      obtain ⟨v, r⟩ := z
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r, rfl, rfl⟩

/-! #### The spine -/

/-- The first (leftmost) term of an expression's left-associative chain. -/
def AExpr.seed : AExpr → ATerm
  | .single t => t
  | .add e _  => e.seed

/-- The `+`-chained step terms after the seed, in order. -/
def AExpr.steps : AExpr → List ATerm
  | .single _ => []
  | .add e t  => e.steps ++ [t]

/-- An expression *is* its seed left-folded over its steps. -/
theorem AExpr.fold_spine : ∀ e : AExpr,
    e.steps.foldl (fun a t => AExpr.add a t) (AExpr.single e.seed) = e
  | .single _ => rfl
  | .add e' t => by
      simp only [AExpr.seed, AExpr.steps, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [AExpr.fold_spine e']

/-- `flatten` follows the spine: the seed's flattening, then `+ tᵢ` for each step. -/
theorem AExpr.flatten_spine : ∀ e : AExpr,
    e.flatten = e.seed.flatten ++ e.steps.flatMap (fun t => '+' :: t.flatten)
  | .single _ => by simp [AExpr.flatten, AExpr.seed, AExpr.steps]
  | .add e' t => by
      simp only [AExpr.seed, AExpr.steps, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [show (AExpr.add e' t).flatten = e'.flatten ++ ('+' :: t.flatten) from rfl,
        AExpr.flatten_spine e', List.append_assoc]

/-! #### The round-trip -/

/-- Both trees at once, by strong induction on the flattened length. `term` accepts any continuation
(self-delimiting); `expr` needs `rest` to not start with `+` (else the greedy fold consumes it). -/
theorem roundtrip_all (n : Nat) :
    (∀ t : ATerm, t.flatten.length = n → ∀ rest,
        (parseTerm (t.flatten ++ rest)).map (fun z => (z.1, z.2.val)) = some (t, rest)) ∧
    (∀ e : AExpr, e.flatten.length = n → ∀ rest, rest.head? ≠ some '+' →
        (parseExpr (e.flatten ++ rest)).map (fun z => (z.1, z.2.val)) = some (e, rest)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    -- `term` round-trip at length `n`
    have hterm : ∀ t : ATerm, t.flatten.length = n → ∀ rest,
        (parseTerm (t.flatten ++ rest)).map (fun z => (z.1, z.2.val)) = some (t, rest) := by
      intro t hn rest
      cases t with
      | digit d =>
        have hd : d.val.isDigit = true := d.property
        have hne : d.val ≠ '(' := by intro h; rw [h] at hd; exact absurd hd (by decide)
        show (parseTerm (d.val :: rest)).map _ = _
        rw [parseTerm, tok_parse_miss rest hne, sat_parse_hit hd rest]
        rfl
      | paren e =>
        have hlen : e.flatten.length < n := by
          rw [← hn]; simp only [ATerm.flatten, List.length_cons, List.length_append]; omega
        have hin : (ATerm.paren e).flatten ++ rest = '(' :: (e.flatten ++ ')' :: rest) := by
          simp [ATerm.flatten, List.append_assoc]
        have hexpr := (ih e.flatten.length hlen).2 e rfl (')' :: rest) (by simp)
        obtain ⟨r2, hpe, hr2⟩ := map_proj_eq_some hexpr
        rw [hin, parseTerm, tok_parse_hit]
        dsimp only
        rw [hpe]
        dsimp only
        split
        · next fst r3 heq =>
          have e1 := tok_consumed heq
          have hr3v : r3.val = rest := by simpa using e1.trans hr2
          simp only [Option.map_some, hr3v]
        · next heq =>
          exfalso
          rw [hr2, tok_parse_hit] at heq
          simp at heq
    -- `term` round-trip for length `≤ n` (seed can equal `n`; steps are `< n`)
    have htermLE : ∀ t : ATerm, t.flatten.length ≤ n → ∀ rest,
        (parseTerm (t.flatten ++ rest)).map (fun z => (z.1, z.2.val)) = some (t, rest) := by
      intro t ht rest
      rcases Nat.lt_or_eq_of_le ht with hlt | heq
      · exact (ih t.flatten.length hlt).1 t rfl rest
      · exact hterm t heq rest
    -- the greedy fold rebuilds the chain
    have haddtail : ∀ (steps : List ATerm), (∀ t ∈ steps, t.flatten.length < n) →
        ∀ (acc : AExpr) (rest : List Char), rest.head? ≠ some '+' →
        (parseAddTail acc (steps.flatMap (fun t => '+' :: t.flatten) ++ rest)).1
            = steps.foldl (fun a t => AExpr.add a t) acc ∧
          (parseAddTail acc (steps.flatMap (fun t => '+' :: t.flatten) ++ rest)).2.val = rest := by
      intro steps
      induction steps with
      | nil =>
        intro _ acc rest hrest
        have hmiss : tokParse '+' rest = none := by
          cases rest with
          | nil => rfl
          | cons c cs => refine tok_parse_miss cs ?_; intro h; subst h; exact hrest rfl
        show (parseAddTail acc rest).1 = acc ∧ (parseAddTail acc rest).2.val = rest
        rw [parseAddTail, hmiss]
        exact ⟨rfl, rfl⟩
      | cons t ts iht =>
        intro hlen acc rest hrest
        have hstep : t.flatten.length < n := hlen t List.mem_cons_self
        have hin : (t :: ts).flatMap (fun t => '+' :: t.flatten) ++ rest
            = '+' :: (t.flatten ++ (ts.flatMap (fun t => '+' :: t.flatten) ++ rest)) := by
          simp [List.flatMap_cons, List.append_assoc]
        have htc := (ih t.flatten.length hstep).1 t rfl
                      (ts.flatMap (fun t => '+' :: t.flatten) ++ rest)
        obtain ⟨r2, hpt, hr2⟩ := map_proj_eq_some htc
        have hrec := iht (fun t' ht' => hlen t' (List.mem_cons_of_mem _ ht')) (AExpr.add acc t) rest hrest
        rw [hin, parseAddTail, tok_parse_hit]
        dsimp only
        rw [hpt]
        dsimp only
        rw [hr2]
        refine ⟨?_, hrec.2⟩
        rw [List.foldl_cons]
        exact hrec.1
    refine ⟨hterm, ?_⟩
    -- `expr` round-trip at length `n`, via the spine
    intro e hn rest hrest
    have hseedLE : e.seed.flatten.length ≤ n := by
      rw [← hn, AExpr.flatten_spine e]; simp only [List.length_append]; omega
    have hstepsLT : ∀ t ∈ e.steps, t.flatten.length < n := by
      have hmem : ∀ (l : List ATerm) (t : ATerm), t ∈ l →
          t.flatten.length < (l.flatMap (fun t => '+' :: t.flatten)).length := by
        intro l
        induction l with
        | nil => intro t ht; simp at ht
        | cons a as ih' =>
          intro t ht
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          rcases List.mem_cons.mp ht with rfl | hm
          · omega
          · have := ih' t hm; omega
      intro t ht
      have h1 := hmem e.steps t ht
      have h2 : e.flatten.length
          = e.seed.flatten.length + (e.steps.flatMap (fun t => '+' :: t.flatten)).length := by
        rw [AExpr.flatten_spine e, List.length_append]
      omega
    have hseed := htermLE e.seed hseedLE (e.steps.flatMap (fun t => '+' :: t.flatten) ++ rest)
    obtain ⟨s1, hps, hs1⟩ := map_proj_eq_some hseed
    have hat := haddtail e.steps hstepsLT (AExpr.single e.seed) rest hrest
    rw [AExpr.flatten_spine e, parseExpr, List.append_assoc, hps]
    dsimp only
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    rw [hs1]
    exact ⟨hat.1.trans (AExpr.fold_spine e), hat.2⟩

/-- **The round-trip law, terminally**: print a tree, parse it back, recover it with nothing left. -/
theorem parseExpr_print (e : AExpr) :
    (parseExpr e.flatten).map (fun z => (z.1, z.2.val)) = some (e, []) := by
  have h := (roundtrip_all e.flatten.length).2 e rfl [] (by simp)
  rw [List.append_nil] at h; exact h

end Recursive

/-! ## The language: a real plug-in vernacular on the `IsoParser` mixfix

Types are the three number sets `N`, `Z`, `R`. Terms are the **mixfix** arithmetic grammar —
parentheses, application by juxtaposition, `*` binding tighter than `+` — built on the
self-contained `IsoParser.Mixfix` stack (abstract token alphabet, explicit `rank`), with no
`CBiparser` dependency.

A language author supplies exactly a `Grammar` (operators, precedence with explicit `rank`) plus the
two boundary adapters. The grammar is *lighter* than the CBiparser one: no `tighter_wf`,
`juxtUnique`, `headsDistinct`, or `interiorTerminates` — the parser needs only the precedence rank.

### ⚠ The round-trip law here is CONDITIONAL

`Mixfix.mixfix`'s `ok` (the greedy left-associative round-trip) is still an open `sorry`, so
`arithLanguage`'s round-trip laws depend on `sorryAx`. The parser itself does not: it `#eval`s and
runs. Discharging that one lemma turns these laws unconditional with no change here.

Note the contrast with `Recursive` above: that section proves exactly this shape of greedy
left-associative reconstruction by hand, for a fixed grammar.
-/

open LambdaLab.IsoParser LambdaLab.IsoParser.Mixfix LambdaLab.Language1

/-- A token literal of the vernacular's alphabet. -/
def tkA (s : String) (h : CBiparser.isToken isSep s = true := by decide) : Token := ⟨s, h⟩

/-- Operators: parentheses, application (juxtaposition), `_ * _`, `_ + _`. -/
inductive ASym | paren | app | times | plus
  deriving DecidableEq, Repr

/-- The tokens `isVar` must reject — including the vernacular keywords, so `def` is not a variable. -/
def aReserved : List Token :=
  [tkA "(", tkA ")", tkA "+", tkA "*", tkA "def", tkA ":", tkA ":="]

def aTighter : ASym → List ASym
  | .plus  => [.times]
  | .times => [.app]
  | .app   => [.paren]
  | .paren => []

def aRank : ASym → Nat
  | .paren => 0 | .app => 1 | .times => 2 | .plus => 3

def aOp : ASym → Operator Token Unit
  | .paren => .closed (.cons (tkA "(") () (.last (tkA ")")))
  | .app   => .juxt
  | .times => .infxl (.last (tkA "*"))
  | .plus  => .infxl (.last (tkA "+"))

def aEntry : Entry Token Unit where
  Op := ASym
  operator := aOp
  ops := [.paren, .app, .times, .plus]
  ops_complete := by intro o; cases o <;> decide
  loosest := [.plus]
  tighter := aTighter
  rank := aRank
  topRank := 4
  rank_tighter := by intro a b h; cases a <;> cases b <;> simp_all [aTighter, aRank]
  rank_lt_topRank := by intro o; cases o <;> decide
  isVar := fun t => decide (t ∉ aReserved)

/-- The grammar — much lighter than the CBiparser one: precedence `rank` and nothing else. -/
def aGrammar : Grammar Token where
  Ent := Unit
  entry := fun _ => aEntry

/-! ### Types: the three number sets -/

/-- `N`, `Z`, `R`. -/
def isNumSet (t : Token) : Bool :=
  t.val == "N" || t.val == "Z" || t.val == "R"

abbrev NumSet := { t : Token // isNumSet t = true }

/-! ### The language -/

/-- The term parser stops at a command boundary. **Derived**, not declared. -/
theorem follow_def : follow (G := aGrammar) () (tkA "def") = true := by decide

def arithLanguage : Language where
  Tm := Expr aGrammar () .loosest
  Ty := NumSet

  -- types: a single token drawn from {N, Z, R}. FOLLOW is ⊤, so `:=` may follow.
  pTy := ((sat isNumSet).weakenFollow (fun _ _ => trivial)).enlargeFirst
    (fun _ hf => absurd trivial hf)

  -- terms: the mixfix parser. Its FIRST is already `anyTok`; its FOLLOW is the grammar's,
  -- narrowed to `def` — sound exactly because `def` is in it (`follow_def`).
  pTm :=
    (mixfix (G := aGrammar) () .loosest).weakenFollow
      (by
        intro t ht
        have h : t = kwDef := ht
        subst h
        exact follow_def)

end LambdaLab.Arith
