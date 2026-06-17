/-!
# Generic `List.takeWhile`/`dropWhile` lemmas

Alphabet-agnostic facts about `takeWhile`/`dropWhile` that the tokenizer and its
correctness proof rely on. Nothing here mentions `Token`, whitespace, or the
grammar — just `p : α → Bool`.
-/

namespace LambdaLab.Parser.Tokenizer

theorem length_dropWhile_le (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    rw [List.dropWhile_cons]
    split
    · exact Nat.le_succ_of_le (length_dropWhile_le p cs)
    · exact Nat.le_refl _

/-- The head of a `dropWhile p` list fails `p` (it is where dropping stopped). -/
theorem not_p_head_dropWhile (p : α → Bool) :
    ∀ {l : List α} {c r}, l.dropWhile p = c :: r → p c = false
  | [], _, _, h => by simp [List.dropWhile] at h
  | a :: as, c, r, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact not_p_head_dropWhile p h
    · next hpa => cases h; simpa using hpa

theorem dropWhile_append_of_all {p : α → Bool} :
    ∀ {g : List α}, (∀ c ∈ g, p c) → ∀ rest, (g ++ rest).dropWhile p = rest.dropWhile p
  | [], _, _ => rfl
  | a :: as, hg, rest => by
    have ha : p a := hg a (by simp)
    have has : ∀ c ∈ as, p c := fun c hc => hg c (by simp [hc])
    rw [List.cons_append, List.dropWhile_cons]; simp [ha, dropWhile_append_of_all has rest]

theorem dropWhile_eq_nil_of_all {p : α → Bool} {l : List α} (h : ∀ c ∈ l, p c) :
    l.dropWhile p = [] := by
  have := dropWhile_append_of_all h []; simpa using this

theorem all_of_dropWhile_eq_nil {p : α → Bool} :
    ∀ {l : List α}, l.dropWhile p = [] → ∀ c ∈ l, p c
  | [], _, c, hc => by simp at hc
  | a :: as, h, c, hc => by
    rw [List.dropWhile_cons] at h
    split at h
    · next ha =>
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact ha
        · exact all_of_dropWhile_eq_nil h c hc'
    · simp at h

/-- `takeWhile` of `w ++ rest` is `w` when every char of `w` satisfies `p` and
`rest` is empty or fails `p` at its head. -/
theorem takeWhile_append_eq {p : α → Bool} :
    ∀ {w rest : List α}, (∀ c ∈ w, p c) → (∀ a r, rest = a :: r → p a = false) →
      (w ++ rest).takeWhile p = w
  | [], rest, _, hr => by
    cases rest with
    | nil => rfl
    | cons a r => rw [List.nil_append, List.takeWhile_cons]; simp [hr a r rfl]
  | a :: as, rest, hw, hr => by
    have ha : p a := hw a (by simp)
    have has : ∀ c ∈ as, p c := fun c hc => hw c (by simp [hc])
    rw [List.cons_append, List.takeWhile_cons]; simp [ha, takeWhile_append_eq has hr]

/-- `dropWhile` of `w ++ rest` is `rest` under the same hypotheses. -/
theorem dropWhile_append_eq {p : α → Bool} :
    ∀ {w rest : List α}, (∀ c ∈ w, p c) → (∀ a r, rest = a :: r → p a = false) →
      (w ++ rest).dropWhile p = rest
  | [], rest, _, hr => by
    cases rest with
    | nil => rfl
    | cons a r => rw [List.nil_append, List.dropWhile_cons]; simp [hr a r rfl]
  | a :: as, rest, hw, hr => by
    have ha : p a := hw a (by simp)
    have has : ∀ c ∈ as, p c := fun c hc => hw c (by simp [hc])
    rw [List.cons_append, List.dropWhile_cons]; simp [ha, dropWhile_append_eq has hr]

theorem mem_takeWhile {p : α → Bool} : ∀ {l : List α} {x}, x ∈ l.takeWhile p → p x
  | a :: as, x, hx => by
    rw [List.takeWhile_cons] at hx
    split at hx
    · next ha =>
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha
        · exact mem_takeWhile hx'
    · simp at hx

end LambdaLab.Parser.Tokenizer
