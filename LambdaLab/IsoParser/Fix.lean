import LambdaLab.IsoParser.Basic

/-!
# `fixParse` — the well-founded recursion core for recursive grammars

Recursive grammars (parens, cross-entry holes) can't be static combinator *values* in a total
language — the definition would be cyclic. The escape is recursion on **input length**: the body gets
a recursor callable only on strictly-shorter input, so it must consume before recursing.

`fixParse` is that core (the parse side). Wrapping it as a law-carrying `IsoParser` — proving
`parse_print` by induction on the value and `print_parse` by induction on input length — is the
remaining `fix` combinator; this pins down the compute first.
-/

namespace LambdaLab.IsoParser

variable {α : Type}

/-- Define a parser by well-founded recursion on input length. The body receives a recursor valid
only on strictly-shorter inputs. -/
def fixParse {v : Type}
    (body : (input : List α) →
      ((input' : List α) → input'.length < input.length →
        Option (v × { r : List α // r.length < input'.length })) →
      Option (v × { r : List α // r.length < input.length })) :
    (input : List α) → Option (v × { r : List α // r.length < input.length })
  | input => body input (fun input' _ => fixParse body input')
  termination_by input => input.length
  decreasing_by exact ‹_›

/-! ## Demonstration: nested parens `( ( x ) )`, a genuinely recursive grammar -/

/-- A nesting: a leaf `x`, or a parenthesized nesting. -/
inductive Paren where
  | leaf : Paren
  | nest : Paren → Paren
  deriving Repr

/-- Structural print. -/
def Paren.flatten : Paren → List Char
  | .leaf   => ['x']
  | .nest p => '(' :: (p.flatten ++ [')'])

/-- Parse a nesting, well-founded recursion on input length (a concrete instance of `fixParse`;
written directly so its equation lemmas drive the law proofs). -/
def parseParen : (input : List Char) → Option (Paren × { r : List Char // r.length < input.length })
  | [] => none
  | c :: rest =>
    if c = 'x' then some (.leaf, ⟨rest, by simp⟩)
    else if c = '(' then
      match parseParen rest with
      | some (p, r) =>
        match hr : r.val with
        | ')' :: r2 => some (.nest p, ⟨r2, by
            have := r.property; rw [hr] at this
            simp only [List.length_cons] at this ⊢; omega⟩)
        | _ => none
      | none => none
    else none
  termination_by input => input.length
  decreasing_by simp_wf

/-- Round-trip a nesting string. -/
def parenRoundtrip (s : String) : Option String :=
  match parseParen s.toList with
  | some (p, r) => if r.val = [] then some (String.ofList p.flatten) else none
  | _ => none

#eval parenRoundtrip "x"        -- some "x"
#eval parenRoundtrip "(x)"      -- some "(x)"
#eval parenRoundtrip "((x))"    -- some "((x))"
#eval parenRoundtrip "(((x)))"  -- some "(((x)))"
#eval parenRoundtrip "((x)"     -- none  (unbalanced)
#eval parenRoundtrip "(y)"      -- none

/-! ## Unfolding lemmas for `parseParen` (the WF `fix` equation, at each head token) -/

theorem parseParen_x (rest : List Char) :
    parseParen ('x' :: rest) = some (Paren.leaf, ⟨rest, by simp⟩) := by
  simp [parseParen]

theorem parseParen_open (rest : List Char) :
    parseParen ('(' :: rest) =
      (match parseParen rest with
        | some (p, r) =>
          match hr : r.val with
          | ')' :: r2 => some (Paren.nest p, ⟨r2, by
              have := r.property; rw [hr] at this
              simp only [List.length_cons] at this ⊢; omega⟩)
          | _ => none
        | none => none) := by
  rw [parseParen]; rw [if_neg (by decide), if_pos rfl]

theorem parseParen_other (c : Char) (rest : List Char) (hx : c ≠ 'x') (hp : c ≠ '(') :
    parseParen (c :: rest) = none := by
  rw [parseParen]; rw [if_neg hx, if_neg hp]

/-! ## The two laws — the `fix` proof, concrete -/

/-- **Round-trip.** Printing a nesting then parsing recovers it (any `rest`). By induction on the
value; the recursive position (inside `(` `)`) uses the IH, and `)` stops the sub-parser exactly. -/
theorem parseParen_roundtrip (p : Paren) (rest : List Char) :
    (parseParen (p.flatten ++ rest)).map (fun z => (z.1, z.2.val)) = some (p, rest) := by
  induction p generalizing rest with
  | leaf =>
    rw [show Paren.leaf.flatten ++ rest = 'x' :: rest from rfl, parseParen_x]; rfl
  | nest q ih =>
    rw [show (Paren.nest q).flatten ++ rest = '(' :: (q.flatten ++ (')' :: rest)) by
      simp [Paren.flatten, List.append_assoc], parseParen_open]
    have hih := ih (')' :: rest)
    rcases hpp : parseParen (q.flatten ++ (')' :: rest)) with _ | ⟨q', r⟩
    · rw [hpp] at hih; simp at hih
    · rw [hpp] at hih
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hih
      obtain ⟨rfl, hrv⟩ := hih
      obtain ⟨rval, rlt⟩ := r
      subst hrv; rfl

/-- **Exactness (soundness).** Whatever `parseParen` consumed, `flatten` reproduces. Strong
induction on input length; the recursive position uses the IH on the shorter interior. -/
theorem parseParen_sound : ∀ (n : Nat) (input : List Char), input.length = n →
    ∀ (p : Paren) (r : { r : List Char // r.length < input.length }),
      parseParen input = some (p, r) → p.flatten ++ r.val = input := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro input hn
    rcases input with _ | ⟨c, rest⟩
    · intro p r h; rw [parseParen] at h; simp at h
    · intro p r h
      by_cases hx : c = 'x'
      · subst hx; rw [parseParen_x] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl
      · by_cases hp : c = '('
        · subst hp; rw [parseParen_open] at h
          split at h
          · rename_i a b hpp
            split at h
            · rename_i r2 heq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hq := ih rest.length (by rw [← hn]; simp) rest rfl a b hpp
              rw [heq] at hq
              simp only [Paren.flatten, List.cons_append, List.append_assoc, List.nil_append]
              rw [hq]
            · exact absurd h.symm (Option.some_ne_none _)
          · exact absurd h.symm (Option.some_ne_none _)
        · rw [parseParen_other c rest hx hp] at h; simp at h

/-- **The recursive parser as a genuine law-carrying `IsoParser`.** A `fix`-style parser (nested
parens) with both round-trip and exactness verified — recursion, sorry-free, in the `IsoParser`
framework. FIRST = `{ '(' , 'x' }`, FOLLOW = `⊤` (self-delimiting). -/
def parenIso : IsoParser Char (fun c => c == '(' || c == 'x') (fun _ => true) Paren (fun _ => PUnit) where
  parse input := (parseParen input).map (fun z => (⟨z.1, PUnit.unit⟩, z.2))
  print p _ := p.flatten
  firstOk c rest hc := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
    simp [parseParen_other c rest hc.2 hc.1]
  parse_print p a rest _ := by
    obtain ⟨⟩ := a
    have hrt := parseParen_roundtrip p rest
    rcases hpp : parseParen (p.flatten ++ rest) with _ | ⟨p', r⟩
    · rw [hpp] at hrt; simp at hrt
    · rw [hpp] at hrt
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨rfl, hrv⟩ := hrt
      simp [hrv]
  print_parse input pa r h := by
    rcases hpp : parseParen input with _ | ⟨p', r'⟩
    · rw [hpp] at h; simp at h
    · rw [hpp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hpa, rfl⟩ := h
      subst hpa
      exact parseParen_sound input.length input rfl p' r' hpp

end LambdaLab.IsoParser
