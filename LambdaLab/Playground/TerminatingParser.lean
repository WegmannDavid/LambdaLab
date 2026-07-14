
abbrev Parser (α : Type) := List Char → Option (α × List Char)

instance : Monad Parser where
  pure a input := some (a, input)
  bind p f input := do
    let (a, rest) ← p input
    f a rest

def pChar (c : Char) : Parser Char := fun input =>
  match input with
  | [] => none
  | hd :: tl => if hd = c then some (hd, tl) else none

instance : Alternative Parser where
  failure := fun _ => none
  orElse p1 p2 := λ input =>
    match p1 input with
    | some res => some res
    | none => p2 () input

/-- A parser **makes progress** when every successful parse leaves a strictly
shorter input. `many` can only terminate for such parsers — otherwise
`many (pure x)` would loop forever, consuming nothing each round. -/
def Progresses (p : Parser α) : Prop :=
  ∀ input x rest, p input = some (x, rest) → rest.length < input.length

/-- Zero-or-more `p`, terminating: the recursion is well-founded on `input.length`,
which `hp` guarantees shrinks every round. Always succeeds (0 matches is fine). -/
def manyCore (p : Parser α) (hp : Progresses p) (input : List Char) : List α × List Char :=
  match h : p input with
  | none => ([], input)
  | some (x, rest) =>
      have _hlt : rest.length < input.length := hp input x rest h
      let (xs, rest') := manyCore p hp rest
      (x :: xs, rest')
termination_by input.length
decreasing_by exact _hlt

def many (p : Parser α) (hp : Progresses p) : Parser (List α) :=
  fun input => some (manyCore p hp input)

def many1 (p : Parser α) (hp : Progresses p) : Parser (List α) := do
  let x ← p
  let xs ← many p hp
  pure (x :: xs)

def digit : Parser Char := fun input =>
  match input with
  | [] => none
  | hd :: tl => if hd.isDigit then some (hd, tl) else none

theorem digit_progresses : Progresses digit := by
  intro input x rest h
  match input with
  | [] => simp [digit] at h
  | c :: tl =>
      simp only [digit] at h
      split at h
      · obtain ⟨rfl, rfl⟩ := Option.some.inj h
        simp only [List.length_cons]; omega
      · exact absurd h (by simp)

def pDigitList : Parser (List Char) := many1 digit digit_progresses

/-! To iterate `pDigitList` followed by `';'`, that combined parser must make progress
too. Progress **composes**: if the first step of a `do` block makes progress and the
rest never grows the input, the whole block makes progress. (`NonGrowing` = the leftover
is never longer than the input — a property every real parser has, but which the plain
`Parser` type doesn't enforce, so we prove it.) -/

def NonGrowing (p : Parser α) : Prop :=
  ∀ input x rest, p input = some (x, rest) → rest.length ≤ input.length

theorem Progresses.nonGrowing {p : Parser α} (h : Progresses p) : NonGrowing p :=
  fun i x r he => Nat.le_of_lt (h i x r he)

/-- Progress threads through `>>=` from the first step. -/
theorem bind_progresses {p : Parser α} {f : α → Parser β}
    (hp : Progresses p) (hf : ∀ a, NonGrowing (f a)) : Progresses (p >>= f) := by
  intro input x rest h
  match hpi : p input with
  | none => simp [Bind.bind, hpi] at h
  | some (a, r) =>
      have h' : f a r = some (x, rest) := by simpa [Bind.bind, hpi] using h
      have := hp input a r hpi
      have := hf a r x rest h'
      omega

theorem bind_nonGrowing {p : Parser α} {f : α → Parser β}
    (hp : NonGrowing p) (hf : ∀ a, NonGrowing (f a)) : NonGrowing (p >>= f) := by
  intro input x rest h
  match hpi : p input with
  | none => simp [Bind.bind, hpi] at h
  | some (a, r) =>
      have h' : f a r = some (x, rest) := by simpa [Bind.bind, hpi] using h
      have := hp input a r hpi
      have := hf a r x rest h'
      omega

theorem pChar_nonGrowing (c : Char) : NonGrowing (pChar c) := by
  intro input x rest h
  match input with
  | [] => simp [pChar] at h
  | hd :: tl =>
      simp only [pChar] at h; split at h
      · obtain ⟨rfl, rfl⟩ := Option.some.inj h
        simp only [List.length_cons]; omega
      · exact absurd h (by simp)

theorem pure_nonGrowing (a : α) : NonGrowing (pure a : Parser α) := by
  intro input x rest h
  replace h : some (a, input) = some (x, rest) := h
  obtain ⟨_, rfl⟩ := Option.some.inj h
  omega

/-- `manyCore`'s leftover never grows (well-founded induction, same measure). -/
theorem manyCore_nonGrowing (p : Parser α) (hp : Progresses p) (input : List Char) :
    (manyCore p hp input).2.length ≤ input.length := by
  unfold manyCore
  split
  · simp
  · rename_i x rest h
    have hlt := hp input x rest h
    rcases hm : manyCore p hp rest with ⟨xs, rest'⟩
    have ih := manyCore_nonGrowing p hp rest
    rw [hm] at ih
    dsimp only at ih
    show rest'.length ≤ input.length
    omega
termination_by input.length
decreasing_by exact hlt

theorem many_nonGrowing (p : Parser α) (hp : Progresses p) : NonGrowing (many p hp) := by
  intro input x rest h
  replace h : some (manyCore p hp input) = some (x, rest) := h
  have hmc : manyCore p hp input = (x, rest) := Option.some.inj h
  have hle := manyCore_nonGrowing p hp input
  rw [hmc] at hle
  exact hle

theorem many1_progresses {p : Parser α} (hp : Progresses p) : Progresses (many1 p hp) :=
  bind_progresses hp (fun _ =>
    bind_nonGrowing (many_nonGrowing p hp) (fun _ => pure_nonGrowing _))

def pDigitLists : Parser (List (List Char)) :=
  many1 (do let l ← pDigitList; let _ ← pChar ';'; return l)
        (bind_progresses (many1_progresses digit_progresses)
          (fun _ => bind_nonGrowing (pChar_nonGrowing ';') (fun _ => pure_nonGrowing _)))

#eval digit "123".toList
#eval pDigitList "123".toList
#eval pDigitLists "123;45;6789;".toList
