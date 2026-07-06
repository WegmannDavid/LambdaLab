import LambdaLab.ParserOld.Tokenizer.Basic

/-!
# The reverse relation `Renders`

`Renders ts s` holds when `s` is a valid rendering of the token list `ts`: the
tokens in order, each whitespace-free and non-empty, separated by at least one
whitespace, with arbitrary leading/trailing whitespace. The forward `tokenize`
collapses all that whitespace freedom to a single split, so it is the function
side; `Renders` is the (non-unique) reverse side — this is where the pipeline's
"reverse op introduces redundant whitespace" lives.

Also: `tok_ws_prepend` (leading whitespace is irrelevant to tokenization) and the
inversion helpers used by the correctness proof.
-/

namespace LambdaLab.ParserOld
namespace Tokenizer

/-- A (possibly empty) run of whitespace. -/
def IsWS (g : List Char) : Prop := ∀ c ∈ g, c.isWhitespace = true

/-- A token's characters: non-empty and whitespace-free. -/
def IsWord (w : List Char) : Prop := w ≠ [] ∧ ∀ c ∈ w, c.isWhitespace = false

/-- Rendering with no leading whitespace: each word is followed by its trailing
gap, and that gap must be non-empty whenever another word follows (so words do
not run together — the maximal-munch invariant). The explicit `body` index plus
the equation field make `cases` on a concrete `a :: r` invert cleanly. -/
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

/-- Leading whitespace does not affect tokenization. -/
theorem tok_ws_prepend {g cs : List Char} (hg : IsWS g) : tok (g ++ cs) = tok cs := by
  have hskip : skipWS (g ++ cs) = skipWS cs :=
    dropWhile_append_of_all (fun c hc => hg c hc) cs
  cases h : skipWS cs with
  | nil => rw [tok_nil (by rw [hskip, h]), tok_nil h]
  | cons c rest => rw [tok_cons (by rw [hskip, h]), tok_cons h]

/-! ### Inversion helpers for `RendersCore` -/

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

end Tokenizer
end LambdaLab.ParserOld
