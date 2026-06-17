import LambdaLab.Parser.Basic

/-!
# A whitespace-separated tokenizer

The first stage of the verification pipeline

    file (String) ──tokenize──▶ tokens (List Token) ──parse──▶ Expr ──truncate──▶ …

`tokenize` splits a source string into tokens at whitespace, Agda-style: tokens
are maximal whitespace-free runs, and adjacent tokens *must* be separated by at
least one whitespace character (no maximal-munch lexing of `n+n` into three
tokens — that is the parser's job once a richer lexer lands).

## Fitting the pipeline

Every stage is a **relation** whose forward map is a function (or an all-results
enumeration) and whose reverse is non-unique. Here the forward map `tokenize` is
deterministic, and the non-uniqueness is on the reverse side: a token list can be
rendered back to source with *redundant whitespace*. We name that reverse relation
`Renders` and characterize the forward map by it, exactly mirroring the parser's

    mem_parse_iff : e ∈ parse tkns ↔ e.flatten = tkns

with

    tokenize_eq_iff : tokenize s = ts ↔ Renders ts s.

Composing the two biconditionals (substitute `ts := e.flatten`) gives the front
half of the pipeline as a single relation, `e ∈ parse (tokenize s) ↔ Renders e.flatten s`.
-/

namespace LambdaLab.Parser
namespace Tokenizer

/-- A character is a token character iff it is not whitespace. -/
@[reducible] def isTokChar (c : Char) : Bool := !c.isWhitespace

/-- The leading token of `cs`: its maximal whitespace-free prefix. -/
def word (cs : List Char) : List Char := cs.takeWhile isTokChar

/-- What is left of `cs` after its leading token: drop the maximal
whitespace-free prefix. -/
def afterWord (cs : List Char) : List Char := cs.dropWhile isTokChar

/-! ### Length facts for the well-founded recursion -/

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

/-- Drop the leading run of whitespace. -/
def skipWS (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)

/-- After skipping leading whitespace, dropping the first word strictly shortens
the original list (the first word is non-empty, since its head — where whitespace
dropping stopped — is a token character). -/
theorem length_afterWord_lt {cs : List Char} {c rest}
    (h : skipWS cs = c :: rest) :
    (afterWord (c :: rest)).length < cs.length := by
  have hc : c.isWhitespace = false := not_p_head_dropWhile _ h
  have htc : isTokChar c = true := by simp [isTokChar, hc]
  have h1 : afterWord (c :: rest) = rest.dropWhile isTokChar := by
    unfold afterWord; rw [List.dropWhile_cons]; simp [htc]
  have h2 : (rest.dropWhile isTokChar).length ≤ rest.length := length_dropWhile_le _ _
  have h3 : (skipWS cs).length ≤ cs.length := length_dropWhile_le _ _
  rw [h] at h3; simp only [List.length_cons] at h3
  rw [h1]; omega

/-! ### The tokenizer -/

/-- Split `cs` into tokens: skip leading whitespace, emit the leading word, recurse. -/
def tok (cs : List Char) : List (List Char) :=
  match h : skipWS cs with
  | [] => []
  | c :: rest => word (c :: rest) :: tok (afterWord (c :: rest))
termination_by cs.length
decreasing_by exact length_afterWord_lt h

/-- Tokenize a source string into whitespace-separated `Token`s. -/
def tokenize (s : String) : List Token := (tok s.toList).map String.ofList

#guard tokenize "n + n" = ["n", "+", "n"]
#guard tokenize "\\lambda x . x" = ["\\lambda", "x", ".", "x"]
#guard tokenize "  n  +   n  " = ["n", "+", "n"]
#guard tokenize "n+n" = ["n+n"]
#guard tokenize "" = []

/-! ### The reverse relation

`Renders ts s` holds when `s` is a valid rendering of the token list `ts`: the
tokens in order, each whitespace-free and non-empty, separated by at least one
whitespace, with arbitrary leading/trailing whitespace. The forward `tokenize`
collapses all that whitespace freedom to a single split, so it is the function
side; `Renders` is the (non-unique) reverse side. -/

/-- A (possibly empty) run of whitespace. -/
def IsWS (g : List Char) : Prop := ∀ c ∈ g, c.isWhitespace = true

/-- A token's characters: non-empty and whitespace-free. -/
def IsWord (w : List Char) : Prop := w ≠ [] ∧ ∀ c ∈ w, c.isWhitespace = false

/-- Rendering with no leading whitespace: each word is followed by its trailing
gap, and that gap must be non-empty whenever another word follows (so words do
not run together — the maximal-munch invariant). -/
inductive RendersCore : List (List Char) → List Char → Prop
  | nil  {g} : IsWS g → RendersCore [] g
  | cons {w g cs ws body} : IsWord w → IsWS g → (ws ≠ [] → g ≠ []) → RendersCore ws cs →
      body = w ++ g ++ cs → RendersCore (w :: ws) body

/-- Rendering with optional leading whitespace. -/
def RendersChars (ws : List (List Char)) (cs : List Char) : Prop :=
  ∃ g body, IsWS g ∧ cs = g ++ body ∧ RendersCore ws body

/-- `s` is a whitespace-rendering of the token list `ts`. -/
def Renders (ts : List Token) (s : String) : Prop :=
  RendersChars (ts.map String.toList) s.toList

/-! ### `dropWhile`/`takeWhile` helpers -/

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

/-! ### Unfolding `tok` -/

theorem tok_nil {cs : List Char} (h : skipWS cs = []) : tok cs = [] := by
  rw [tok]; split
  · rfl
  · next c rest h' => rw [h] at h'; exact absurd h' (by simp)

theorem tok_cons {cs : List Char} {c rest} (h : skipWS cs = c :: rest) :
    tok cs = word (c :: rest) :: tok (afterWord (c :: rest)) := by
  rw [tok]; split
  · next h' => rw [h] at h'; exact absurd h' (by simp)
  · next c' rest' h' => rw [h] at h'; cases h'; rfl

/-- Leading whitespace does not affect tokenization. -/
theorem tok_ws_prepend {g cs : List Char} (hg : IsWS g) : tok (g ++ cs) = tok cs := by
  have hskip : skipWS (g ++ cs) = skipWS cs :=
    dropWhile_append_of_all (fun c hc => hg c hc) cs
  cases h : skipWS cs with
  | nil => rw [tok_nil (by rw [hskip, h]), tok_nil h]
  | cons c rest => rw [tok_cons (by rw [hskip, h]), tok_cons h]

/-! ### Inversion helpers for `RendersCore` -/

theorem mem_takeWhile {p : α → Bool} : ∀ {l : List α} {x}, x ∈ l.takeWhile p → p x
  | a :: as, x, hx => by
    rw [List.takeWhile_cons] at hx
    split at hx
    · next ha =>
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha
        · exact mem_takeWhile hx'
    · simp at hx

/-- The head where word-taking stops (= where token-char dropping stops) is whitespace. -/
theorem afterWord_head_ws {cs a r} (h : afterWord cs = a :: r) : a.isWhitespace = true := by
  have h' : cs.dropWhile isTokChar = a :: r := h
  have := not_p_head_dropWhile _ h'
  simp [isTokChar] at this; exact this

/-- A non-empty token list renders to a non-empty string. -/
theorem rendersCore_ne_nil {ws body} (h : RendersCore ws body) (hne : ws ≠ []) : body ≠ [] := by
  cases h with
  | nil => exact absurd rfl hne
  | @cons w g cs ws' body hw _ _ _ hbody =>
      subst hbody; intro hb
      exact hw.1 (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hb).1).1

/-- The first character of a non-empty rendering is a token character (the start
of the first word). -/
theorem rendersCore_head_ws_false {ws a r} (h : RendersCore ws (a :: r)) (hne : ws ≠ []) :
    a.isWhitespace = false := by
  cases h with
  | nil => exact absurd rfl hne
  | @cons w g cs ws' body hw _ _ _ hbody =>
      cases w with
      | nil => exact absurd rfl hw.1
      | cons w0 w' =>
          rw [List.cons_append, List.cons_append] at hbody
          have ha0 : a = w0 := (List.cons.inj hbody).1
          rw [ha0]; exact hw.2 w0 (by simp)

/-! ### The two directions -/

/-- Forward: the actual token split is a valid rendering of the input. -/
theorem tok_renders : (cs : List Char) → RendersChars (tok cs) cs
  | cs => by
    cases h : skipWS cs with
    | nil =>
        rw [tok_nil h]
        exact ⟨cs, [], all_of_dropWhile_eq_nil h, (List.append_nil cs).symm,
               RendersCore.nil (by intro c hc; simp at hc)⟩
    | cons c rest =>
        rw [tok_cons h]
        have hc_tok : isTokChar c = true := by
          have : c.isWhitespace = false := not_p_head_dropWhile _ h
          simp [isTokChar, this]
        obtain ⟨g2, body2, hg2, hcs2, hrc2⟩ := tok_renders (afterWord (c :: rest))
        have hwd : word (c :: rest) ++ afterWord (c :: rest) = c :: rest := by
          unfold word afterWord; exact List.takeWhile_append_dropWhile
        have hword : IsWord (word (c :: rest)) := by
          refine ⟨?_, ?_⟩
          · show (c :: rest).takeWhile isTokChar ≠ []
            rw [List.takeWhile_cons]; simp [hc_tok]
          · intro x hx
            have hx' : x ∈ (c :: rest).takeWhile isTokChar := hx
            have := mem_takeWhile hx'; simp [isTokChar] at this; exact this
        have hsep : tok (afterWord (c :: rest)) ≠ [] → g2 ≠ [] := by
          intro hne hg2nil
          subst hg2nil
          rw [List.nil_append] at hcs2
          have hb2 : body2 ≠ [] := rendersCore_ne_nil hrc2 hne
          cases hbody : body2 with
          | nil => exact hb2 hbody
          | cons a r =>
              have haw : afterWord (c :: rest) = a :: r := by rw [hcs2, hbody]
              have h_ws : a.isWhitespace = true := afterWord_head_ws haw
              have h_nonws : a.isWhitespace = false :=
                rendersCore_head_ws_false (hbody ▸ hrc2) hne
              rw [h_ws] at h_nonws; simp at h_nonws
        have heq : c :: rest = word (c :: rest) ++ g2 ++ body2 := by
          rw [List.append_assoc, ← hcs2, hwd]
        refine ⟨cs.takeWhile (·.isWhitespace), c :: rest,
               (fun x hx => mem_takeWhile hx), ?_,
               RendersCore.cons hword hg2 hsep hrc2 heq⟩
        have hh : (c :: rest) = cs.dropWhile (·.isWhitespace) := h.symm
        rw [hh]; exact List.takeWhile_append_dropWhile.symm
  termination_by cs => cs.length
  decreasing_by exact length_afterWord_lt h

/-- Backward: every valid rendering tokenizes to its token list. (Lean's
`induction` substitutes the inductive hypothesis `tok cs = ws'`, so the goal
already reads in terms of `tok cs`.) -/
theorem rendersCore_tok {ws body} (h : RendersCore ws body) : tok body = ws := by
  induction h with
  | nil hg => exact tok_nil (dropWhile_eq_nil_of_all (fun c hc => hg c hc))
  | @cons w g cs ws' body hw hg hsep hrc hbody ih =>
      rw [hbody, List.append_assoc]
      obtain ⟨w0, w', rfl⟩ : ∃ w0 w', w = w0 :: w' := by
        cases w with
        | nil => exact absurd rfl hw.1
        | cons w0 w' => exact ⟨w0, w', rfl⟩
      have hw0 : w0.isWhitespace = false := hw.2 w0 (by simp)
      have hw_all : ∀ c ∈ w0 :: w', isTokChar c = true := fun c hc => by
        have := hw.2 c hc; simp [isTokChar, this]
      have hr_tok : ∀ a r, g ++ cs = a :: r → isTokChar a = false := by
        intro a r hgcs
        cases g with
        | cons x xs =>
            rw [List.cons_append] at hgcs
            have hx : x.isWhitespace = true := hg x (by simp)
            rw [(List.cons.inj hgcs).1] at hx; simp [isTokChar, hx]
        | nil =>
            rw [List.nil_append] at hgcs
            have hws' : ws' = [] := Classical.byContradiction (fun hne => hsep hne rfl)
            subst hws'
            cases hrc with
            | nil hcsws =>
                have haws : a.isWhitespace = true := hcsws a (by rw [hgcs]; simp)
                simp [isTokChar, haws]
      have hskip : skipWS ((w0 :: w') ++ (g ++ cs)) = w0 :: (w' ++ (g ++ cs)) := by
        simp [skipWS, List.cons_append, hw0]
      rw [tok_cons hskip]
      have hword : word (w0 :: (w' ++ (g ++ cs))) = w0 :: w' :=
        takeWhile_append_eq hw_all hr_tok
      have hafter : afterWord (w0 :: (w' ++ (g ++ cs))) = g ++ cs :=
        dropWhile_append_eq hw_all hr_tok
      rw [hword, hafter, tok_ws_prepend hg, ih]

/-! ### Correctness: the composable `tokenize_eq_iff`

Same shape as the parser's `mem_parse_iff`, so the biconditionals chain. -/

theorem tok_eq_iff {cs : List Char} {ws : List (List Char)} :
    tok cs = ws ↔ RendersChars ws cs := by
  constructor
  · intro h; rw [← h]; exact tok_renders cs
  · rintro ⟨g, body, hg, rfl, hrc⟩
    rw [tok_ws_prepend hg]; exact rendersCore_tok hrc

theorem tokenize_eq_iff {s : String} {ts : List Token} :
    tokenize s = ts ↔ Renders ts s := by
  rw [Renders, ← tok_eq_iff, tokenize]
  constructor
  · intro h
    rw [← h, List.map_map]
    have hid : (String.toList ∘ String.ofList) = id := funext fun _ => String.toList_ofList
    rw [hid, List.map_id]
  · intro h
    rw [h, List.map_map]
    have hid : (String.ofList ∘ String.toList) = id := funext fun _ => String.ofList_toList
    rw [hid, List.map_id]

end Tokenizer
end LambdaLab.Parser
