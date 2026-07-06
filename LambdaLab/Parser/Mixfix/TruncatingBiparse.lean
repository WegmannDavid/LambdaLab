import LambdaLab.Parser.Mixfix.Biparse
import LambdaLab.Parser.Mixfix.Truncation

/-!
# Bolting truncation onto the char `Biparser`

A `ReverseInterp G` at a start entry `e`, together with a **chosen policy `p`**,
composes with the char `Biparser` into a `TruncatingBiparser Char (eInt e)`:

* `parse` — the char prefix parser (`parseChars`), each surface tree `truncate`d to
  a carrier value;
* `render` — `lift` a value back to its minimally-parenthesized surface tree, then
  render it char-level under `p` (`renderExpr`) — so the render policy still runs on
  `Expr`, exactly where it can see the parentheses. The policy is **baked in**, so the
  result exposes no `Policy` type parameter (keeping it universe-flat for `Language`).

Only `parse_complete` survives (truncation is lossy — see `TruncatingBiparser`). It
falls straight out of `truncate_lift` (reverse round-trip on carrier values) and the
lossless `Biparser`'s `char_parse_complete`.
-/

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

/-- Bundle a `ReverseInterp` at start entry `e` with a chosen policy `p` as a
`TruncatingBiparser` over chars: `render = renderExpr · p ∘ lift`,
`parse = truncate ∘ parseChars`. -/
def ReverseInterp.toTruncatingBiparser {G : Grammar} (t : ReverseInterp G) (e : G.Ent)
    (p : Policy G) : TruncatingBiparser Char (t.eInt e) where
  render v := renderExpr (t.lift e v) p
  parse cs := (parseChars e cs).map (fun x => (Expr.truncate t.toInterp x.1, x.2))
  parse_complete := by
    intro v rest
    obtain ⟨s, hs, hm⟩ := char_parse_complete (t.lift e v) p rest
    exact ⟨s, hs, List.mem_map.mpr ⟨(t.lift e v, s), hm, by rw [t.truncate_lift]⟩⟩

end LambdaLab.Parser.Mixfix
