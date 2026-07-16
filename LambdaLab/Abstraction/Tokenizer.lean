import LambdaLab.Abstraction.Basic
import LambdaLab.CBiparser.Tokenizer

/-!
# The tokenizer as a morphism of `Abs`

`List Char ⇝ List Token`. The lossy map is `tokens` (tokenize), which forgets the exact separators.

The annotation type is **`List Char` itself** — the concrete string is its own faithful annotation.
That is not a cop-out: a token list *with its gaps* is isomorphic to the char string it came from
(the gaps are exactly the separators the string already contains), so the char string is the
canonical maximal annotation, and it keeps the instance to the four obvious maps with no new type.

* `abstract = forget = tokens` — tokenize, on either the concrete or the annotated (same type).
* `realize  = id`             — the annotation *is* the concrete string.
* `annotate = render (…)`     — attach a canonical single-separator gap between tokens.

Where the content lives: `abstract_realize` and `realize_surj` are trivial (`realize = id`); the one
law that says something is **`forget_annotate`** — render a token list, tokenize it back, recover the
tokens — which is `tokens_render_append` at end-of-input.

Composition-wise this is the right choice: for `tokenizer ≫ parser` the shared foot is `List Token`
and `forget = tokens`, so the pullback pairs a char string with a parse consistent with its tokens —
whitespace on one side, parentheses on the other, exactly as intended.
-/

namespace LambdaLab.Abstraction

open LambdaLab.CBiparser

/-- The tokenizer for separator predicate `sep`, with a witness separator `sc` used as the canonical
inter-token gap, as an abstraction `List Char ⇝ List Token`. -/
def tokenizer (sep : Char → Bool) (sc : Char) (hsc : sep sc = true) :
    Abstraction (List Char) (List (Token sep)) (List Char) where
  abstract := tokens sep
  realize  := _root_.id
  forget   := tokens sep
  annotate := render (fun _ _ => [sc])
  abstract_realize := fun _ => rfl
  realize_surj     := fun x => ⟨x, rfl⟩
  forget_annotate  := fun ts => by
    have hgap : ∀ t u : Token sep, Gap sep ((fun _ _ => [sc]) t u) := fun _ _ =>
      ⟨fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact hsc, by simp⟩
    have hnil : tokens sep ([] : List Char) = [] := by simp [tokens]
    have h := tokens_render_append hgap ts (rest := []) (by simp)
    simp only [List.append_nil, hnil] at h
    exact h

end LambdaLab.Abstraction
