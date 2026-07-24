import LambdaLab.Parser.IsoParser.Combinators

/-!
# `gdo` — do-notation for the indexed monad

`bind` is an *indexed* monadic bind — FIRST/FOLLOW change across it — so Lean's `Bind`/`do`
cannot apply; and each bind carries a seam obligation (`FIRST(k) ⊆ FOLLOW(p)`). The `gdo` macro
provides the do-syntax, threading each seam as `(by seam)`.

The seams are the lexical facts that make the grammar unambiguous. `seam` tries the common
shapes: `trivial` for a `⊤` FOLLOW, `assumption`/`simp_all` for definitional ones, `decide` for
decidable atoms (e.g. `¬('B'.isDigit = true)`). Bring anything unusual into scope with `have`
before the block.
-/

namespace LambdaLab.Parser.IsoParser

/-- Discharge a `bind` seam: `∀ c, FIRST₂ c → FOLLOW₁ c`. -/
macro "seam" : tactic => `(tactic| (
  intro c hc
  first
    | trivial
    | assumption
    | simp_all
    | decide))

syntax "gdo " ("let " ident " ← " term ";"?)+ "return " term : term

macro_rules
  | `(gdo $[let $xs ← $ps $[;]?]* return $e) => do
      let n := xs.size
      let mut acc ← `(map (fun $(xs[n-1]!) => $e) $(ps[n-1]!))
      for i in [0:n-1] do
        let j := n - 2 - i
        acc ← `(bind $(ps[j]!) (fun $(xs[j]!) => $acc) (by seam))
      return acc

end LambdaLab.Parser.IsoParser
