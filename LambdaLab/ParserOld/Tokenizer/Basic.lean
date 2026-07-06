import LambdaLab.ParserOld.Basic
import LambdaLab.ParserOld.Tokenizer.ListLemmas

/-!
# The tokenizer: definitions

`tokenize` splits a source string into tokens at whitespace, Agda-style: tokens
are maximal whitespace-free runs, and adjacent tokens *must* be separated by at
least one whitespace character (no maximal-munch lexing of `n+n` into three
tokens — that is the parser's job once a richer lexer lands).

Internally we work over `List Char`: `tok` skips leading whitespace, emits the
leading word, and recurses; `tokenize` lifts it to `String`/`Token`. The
unfolding lemmas `tok_nil`/`tok_cons` expose the one-step behaviour to the proofs.
-/

namespace LambdaLab.ParserOld
namespace Tokenizer

/-- A character is a token character iff it is not whitespace. -/
@[reducible] def isTokChar (c : Char) : Bool := !c.isWhitespace

/-- The leading token of `cs`: its maximal whitespace-free prefix. -/
def word (cs : List Char) : List Char := cs.takeWhile isTokChar

/-- What is left of `cs` after its leading token: drop the maximal
whitespace-free prefix. -/
def afterWord (cs : List Char) : List Char := cs.dropWhile isTokChar

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

end Tokenizer
end LambdaLab.ParserOld
