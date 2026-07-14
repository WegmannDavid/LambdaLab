
def Token : Type := { s : String // ∀ c ∈ s.toList, c.isWhitespace = false } -- string that does not contain whitespace

def Tokens : Type := List Token

/-- Every element kept by `takeWhile` satisfies the predicate. -/
theorem mem_takeWhile_pred {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : a ∈ l.takeWhile p) : p a = true := by
  induction l with
  | nil => simp [List.takeWhile] at h
  | cons hd tl ih =>
      simp only [List.takeWhile] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h'
        · assumption
        · exact ih h'
      · simp at h

/-- Parse a single token: the maximal leading run of non-whitespace characters,
returning it together with the rest of the input. `none` if the input is empty or
starts with whitespace (so a token is always non-empty). -/
def pToken (input : List Char) : Option (Token × List Char) :=
  match h : input.takeWhile (fun c => !c.isWhitespace) with
  | []  => none
  | run =>
      some (⟨String.ofList run, by
              intro c hc
              rw [String.toList_ofList] at hc
              have hmem : c ∈ input.takeWhile (fun c => !c.isWhitespace) := by rw [h]; exact hc
              simpa using mem_takeWhile_pred hmem⟩,
            input.dropWhile (fun c => !c.isWhitespace))
