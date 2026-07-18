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

/-! ## `fix` — the recursion pattern abstracted into a reusable combinator

The `parenIso` proof, generalized: a body describing one layer (with a recursor for shorter inputs)
plus its two step-laws, and `fix` does the well-founded induction once. Trivial annotation. -/

variable {v : Type} {fst fol : α → Bool}

/-- Abbreviation: the body of a recursive parser (trivial annotation). -/
abbrev FixBody (α : Type) (v : Type) :=
  (input : List α) →
    ((input' : List α) → input'.length < input.length →
      Option (v × { r : List α // r.length < input'.length })) →
    Option (v × { r : List α // r.length < input.length })

/-- The round-trip, lifted over the fixpoint by strong induction on input length. -/
theorem fixParse_run (body : FixBody α v) (print : v → List α)
    (h_pp : ∀ (x : v) (rest : List α)
      (rec : (input' : List α) → input'.length < (print x ++ rest).length →
        Option (v × { r : List α // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (y : v) (rest' : List α) (h : (print y ++ rest').length < (print x ++ rest).length),
          HeadIn fol rest' →
          (rec (print y ++ rest') h).map (fun z => (z.1, z.2.val)) = some (y, rest')) →
      (body (print x ++ rest) rec).map (fun z => (z.1, z.2.val)) = some (x, rest)) :
    ∀ (n : Nat) (x : v) (rest : List α), (print x ++ rest).length = n → HeadIn fol rest →
      (fixParse body (print x ++ rest)).map (fun z => (z.1, z.2.val)) = some (x, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x rest hn hr
    rw [fixParse]
    apply h_pp x rest _ hr
    intro y rest' hlt hr'
    exact ih (print y ++ rest').length (hn ▸ hlt) y rest' rfl hr'

/-- Exactness, lifted over the fixpoint by strong induction on input length. -/
theorem fixParse_sound (body : FixBody α v) (print : v → List α)
    (h_sound : ∀ (input : List α)
      (rec : (input' : List α) → input'.length < input.length →
        Option (v × { r : List α // r.length < input'.length })),
      (∀ (input' : List α) (h : input'.length < input.length) (y : v) (r), rec input' h = some (y, r) →
          print y ++ r.val = input') →
      ∀ (x : v) (r), body input rec = some (x, r) → print x ++ r.val = input) :
    ∀ (n : Nat) (input : List α), input.length = n →
      ∀ (x : v) (r), fixParse body input = some (x, r) → print x ++ r.val = input := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro input hn x r h
    rw [fixParse] at h
    refine h_sound input _ ?_ x r h
    intro input' hlt y r0 hrec
    exact ih input'.length (hn ▸ hlt) input' rfl y r0 hrec

/-- **`fix`** — build a recursive parser from a one-layer body and its step-laws. Does the
well-founded induction once; the two laws come from `h_pp`/`h_sound`. -/
def fix (body : FixBody α v) (print : v → List α)
    (h_first : ∀ (c : α) (rest : List α) rec, fst c = false → body (c :: rest) rec = none)
    (h_pp : ∀ (x : v) (rest : List α)
      (rec : (input' : List α) → input'.length < (print x ++ rest).length →
        Option (v × { r : List α // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (y : v) (rest' : List α) (h : (print y ++ rest').length < (print x ++ rest).length),
          HeadIn fol rest' →
          (rec (print y ++ rest') h).map (fun z => (z.1, z.2.val)) = some (y, rest')) →
      (body (print x ++ rest) rec).map (fun z => (z.1, z.2.val)) = some (x, rest))
    (h_sound : ∀ (input : List α)
      (rec : (input' : List α) → input'.length < input.length →
        Option (v × { r : List α // r.length < input'.length })),
      (∀ (input' : List α) (h : input'.length < input.length) (y : v) (r), rec input' h = some (y, r) →
          print y ++ r.val = input') →
      ∀ (x : v) (r), body input rec = some (x, r) → print x ++ r.val = input) :
    IsoParser α fst fol v (fun _ => PUnit) where
  parse input := (fixParse body input).map (fun z => (⟨z.1, PUnit.unit⟩, z.2))
  print x _ := print x
  firstOk c rest hc := by
    rw [fixParse, h_first c rest _ hc]; rfl
  parse_print x a rest hr := by
    obtain ⟨⟩ := a
    have hrt := fixParse_run body print h_pp (print x ++ rest).length x rest rfl hr
    rcases hfp : fixParse body (print x ++ rest) with _ | ⟨x', r⟩
    · rw [hfp] at hrt; simp at hrt
    · rw [hfp] at hrt
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨rfl, hrv⟩ := hrt
      simp [hrv]
  print_parse input pa r h := by
    rcases hfp : fixParse body input with _ | ⟨x', r'⟩
    · rw [hfp] at h; simp at h
    · rw [hfp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hpa, rfl⟩ := h
      subst hpa
      exact fixParse_sound body print h_sound input.length input rfl x' r' hfp

/-! ## `fix2` — the ergonomic version: a **proof-free** recursor

`FixBody`'s recursor took the "shorter" proof as an argument, which coupled the list into a proof and
made the step-laws un-applicable to bracketed grammars (the recursor's arg differs by
append-associativity, and rewriting it hits a dependent-motive wall). `fix2` moves the guard inside:
the recursor takes just a `List α`, and `fixParse2` returns `none` when it isn't shorter. Then relating
`rec A` and `rec B` (`A = B`) across the subtype-erasing `.map` is a plain `congrArg`. -/

/-- Recursor with the shortness guard internalized (no proof argument). -/
abbrev FixBody2 (α : Type) (v : Type) :=
  (input : List α) →
    ((input' : List α) → Option (v × { r : List α // r.length < input'.length })) →
    Option (v × { r : List α // r.length < input.length })

/-- Well-founded fixpoint with a proof-free recursor (guarded internally). -/
def fixParse2 {v : Type} (body : FixBody2 α v) :
    (input : List α) → Option (v × { r : List α // r.length < input.length })
  | input => body input (fun input' => if h : input'.length < input.length then fixParse2 body input' else none)
  termination_by input => input.length
  decreasing_by exact h

variable {v : Type} {fst fol : α → Bool}

theorem fixParse2_run (body : FixBody2 α v) (print : v → List α)
    (h_pp : ∀ (x : v) (rest : List α)
      (rec : (input' : List α) → Option (v × { r : List α // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (y : v) (rest' : List α), (print y ++ rest').length < (print x ++ rest).length →
          HeadIn fol rest' → (rec (print y ++ rest')).map (fun z => (z.1, z.2.val)) = some (y, rest')) →
      (body (print x ++ rest) rec).map (fun z => (z.1, z.2.val)) = some (x, rest)) :
    ∀ (n : Nat) (x : v) (rest : List α), (print x ++ rest).length = n → HeadIn fol rest →
      (fixParse2 body (print x ++ rest)).map (fun z => (z.1, z.2.val)) = some (x, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x rest hn hr
    rw [fixParse2]
    apply h_pp x rest _ hr
    intro y rest' hlt hr'
    simp only [dif_pos hlt]
    exact ih (print y ++ rest').length (hn ▸ hlt) y rest' rfl hr'

theorem fixParse2_sound (body : FixBody2 α v) (print : v → List α)
    (h_sound : ∀ (input : List α)
      (rec : (input' : List α) → Option (v × { r : List α // r.length < input'.length })),
      (∀ (input' : List α), input'.length < input.length → ∀ (y : v) (r), rec input' = some (y, r) →
          print y ++ r.val = input') →
      ∀ (x : v) (r), body input rec = some (x, r) → print x ++ r.val = input) :
    ∀ (n : Nat) (input : List α), input.length = n →
      ∀ (x : v) (r), fixParse2 body input = some (x, r) → print x ++ r.val = input := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro input hn x r h
    rw [fixParse2] at h
    refine h_sound input _ ?_ x r h
    intro input' hlt y r0 hrec
    rw [dif_pos hlt] at hrec
    exact ih input'.length (hn ▸ hlt) input' rfl y r0 hrec

/-- **`fix2`** — reusable recursion combinator with the ergonomic proof-free recursor. -/
def fix2 (body : FixBody2 α v) (print : v → List α)
    (h_first : ∀ (c : α) (rest : List α) rec, fst c = false → body (c :: rest) rec = none)
    (h_pp : ∀ (x : v) (rest : List α)
      (rec : (input' : List α) → Option (v × { r : List α // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (y : v) (rest' : List α), (print y ++ rest').length < (print x ++ rest).length →
          HeadIn fol rest' → (rec (print y ++ rest')).map (fun z => (z.1, z.2.val)) = some (y, rest')) →
      (body (print x ++ rest) rec).map (fun z => (z.1, z.2.val)) = some (x, rest))
    (h_sound : ∀ (input : List α)
      (rec : (input' : List α) → Option (v × { r : List α // r.length < input'.length })),
      (∀ (input' : List α), input'.length < input.length → ∀ (y : v) (r), rec input' = some (y, r) →
          print y ++ r.val = input') →
      ∀ (x : v) (r), body input rec = some (x, r) → print x ++ r.val = input) :
    IsoParser α fst fol v (fun _ => PUnit) where
  parse input := (fixParse2 body input).map (fun z => (⟨z.1, PUnit.unit⟩, z.2))
  print x _ := print x
  firstOk c rest hc := by
    rw [fixParse2, h_first c rest _ hc]; rfl
  parse_print x a rest hr := by
    obtain ⟨⟩ := a
    have hrt := fixParse2_run body print h_pp (print x ++ rest).length x rest rfl hr
    rcases hfp : fixParse2 body (print x ++ rest) with _ | ⟨x', r⟩
    · rw [hfp] at hrt; simp at hrt
    · rw [hfp] at hrt
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨rfl, hrv⟩ := hrt
      simp [hrv]
  print_parse input pa r h := by
    rcases hfp : fixParse2 body input with _ | ⟨x', r'⟩
    · rw [hfp] at h; simp at h
    · rw [hfp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hpa, rfl⟩ := h
      subst hpa
      exact fixParse2_sound body print h_sound input.length input rfl x' r' hfp

/-! ## Validating `fix2`: the parens parser rebuilt through it -/

/-- One layer, proof-free recursor. -/
def parenBody2 : FixBody2 Char Paren := fun input rec =>
  match input with
  | [] => none
  | c :: rest =>
    if c = 'x' then some (.leaf, ⟨rest, by simp⟩)
    else if c = '(' then
      match rec rest with
      | some (p, r) =>
        match hr : r.val with
        | ')' :: r2 => some (.nest p, ⟨r2, by
            have h0 := r.property; rw [hr] at h0
            simp only [List.length_cons] at h0 ⊢; omega⟩)
        | _ => none
      | none => none
    else none

/-- **The parens parser via `fix2`** — the step-laws now go through (the `congrArg` transport in
`h_pp` is where the old interface got stuck). -/
def parenViaFix : IsoParser Char (fun c => c == '(' || c == 'x') (fun _ => true) Paren (fun _ => PUnit) :=
  fix2 parenBody2 Paren.flatten
    (h_first := by
      intro c rest rec hc
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      simp only [parenBody2]; rw [if_neg hc.2, if_neg hc.1])
    (h_pp := by
      intro x rest rec _ hrec
      cases x with
      | leaf => simp [parenBody2, Paren.flatten]
      | nest q =>
        show (parenBody2 ('(' :: ((q.flatten ++ [')']) ++ rest)) rec).map (fun z => (z.1, z.2.val))
          = some (Paren.nest q, rest)
        simp only [parenBody2]
        rw [if_neg (by decide)]; simp only [if_true]
        have happ : (q.flatten ++ [')']) ++ rest = q.flatten ++ (')' :: rest) := by
          rw [List.append_assoc]; rfl
        have hq := hrec q (')' :: rest)
          (by simp only [Paren.flatten, List.length_append, List.length_cons]; omega)
          (by intro a _; rfl)
        have hmap : (rec ((q.flatten ++ [')']) ++ rest)).map (fun z => (z.1, z.2.val)) = some (q, ')' :: rest) := by
          rw [congrArg (fun l => (rec l).map (fun z => (z.1, z.2.val))) happ]; exact hq
        rcases hrc : rec ((q.flatten ++ [')']) ++ rest) with _ | ⟨q', r0⟩
        · rw [hrc] at hmap; simp at hmap
        · rw [hrc] at hmap
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
          obtain ⟨rfl, hrv⟩ := hmap
          obtain ⟨r0v, r0lt⟩ := r0
          subst hrv; rfl)
    (h_sound := by
      intro input rec hrec x r h
      match input with
      | [] => simp only [parenBody2] at h; exact absurd h (by simp)
      | c :: rest =>
        by_cases hx : c = 'x'
        · subst hx
          simp only [parenBody2, if_pos] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; rfl
        · by_cases hp : c = '('
          · subst hp
            simp only [parenBody2, if_neg hx, if_pos] at h
            split at h
            · rename_i a b hrb
              split at h
              · rename_i r2 heq
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hb := hrec rest (by simp) a b hrb
                rw [heq] at hb
                simp only [Paren.flatten, List.cons_append, List.append_assoc, List.nil_append]
                rw [hb]
              · exact absurd h.symm (Option.some_ne_none _)
            · exact absurd h.symm (Option.some_ne_none _)
          · simp only [parenBody2, if_neg hx, if_neg hp] at h
            exact absurd h.symm (Option.some_ne_none _))

#eval match parenViaFix.run "((x))".toList with
  | some (⟨p, _⟩, []) => some (String.ofList p.flatten)
  | _ => none                                                   -- some "((x))"

end LambdaLab.IsoParser
