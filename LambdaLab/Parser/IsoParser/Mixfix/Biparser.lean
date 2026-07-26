import LambdaLab.Parser.IsoParser.Mixfix.Complete

/-!
# The general mixfix `IsoParser`

Packages the self-contained mixfix parser as an `IsoParser` over the abstract token alphabet.
**Aligned**: source = value = the tree, `print` is `flatten`.

* **FIRST = ⊤** (`firstOk` vacuous) — exactly what `Language1`'s interface asks for.
* **FOLLOW** carries the content: the computed `follow` (`Complete.lean`) — tokens at which the
  greedy parser provably stops.
* **`ok`** is *derived* (`parseExpr_complete`) from the decomposition in `Complete.lean`, given
  the grammar's two hypotheses.

## The two hypotheses are necessary, not incidental

`mixfix` takes `Lawful G` and `Unambiguous G`. Both are forced:

* without `Unambiguous`, the law is **false** — `Ambiguity.lean` proves it for a grammar with two
  identically-spelled operators (`law_not_universal`), and the argument applies to any
  deterministic parser;
* without `Lawful`'s `interiorTerminates`, the greedy parser runs past the `)` of `( _ )` and a
  printed tree does not parse back.

`Lawful` is decidable for a concrete grammar (`by decide`). `Unambiguous` is not decidable
(it quantifies over all trees), and deriving it from finitely-checkable lexical conditions is
open — see the project notes on `UniqueNameParts` / Danielsson–Norell §4.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

open LambdaLab.Parser.IsoParser

variable {Tok : Type} [DecidableEq Tok] {G : Grammar Tok}

/-- **The general mixfix parser as an `IsoParser`.** Aligned; `print = flatten`. -/
def mixfix (hL : Lawful G) (hU : Unambiguous G) (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser Tok (fun _ => True) (fun t => follow e t = true)
      (Expr G e l) (Expr G e l) where
  parse input := (parseExpr e l input).map (fun z => (z.1, ⟨z.2.list, z.2.lt⟩))
  print t := (t, t.flatten)
  firstOk c rest hc := absurd trivial hc
  ok t rest hrest := by
    have h := parseExpr_complete hL hU t rest hrest
    simp only [runExpr] at h
    simpa [Option.map_map] using h

end LambdaLab.Parser.IsoParser.Mixfix
