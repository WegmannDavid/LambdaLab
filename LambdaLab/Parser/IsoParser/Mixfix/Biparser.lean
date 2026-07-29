import LambdaLab.Parser.IsoParser.Mixfix.Complete

/-!
# The general mixfix `IsoParser`

Packages the self-contained mixfix parser as an `IsoParser` over the abstract token alphabet.
**Aligned**: source = value = the tree, `print` is `flatten`.

* **FIRST = ⊤** (`firstOk` vacuous) — exactly what `Language`'s interface asks for.
* **FOLLOW** carries the content: the computed `follow` (`Complete.lean`) — tokens at which the
  greedy parser provably stops.
* **`ok`** is *derived* (`parseExpr_complete`) from the decomposition in `Complete.lean`, given
  the grammar's two hypotheses.

## The two hypotheses are necessary, not incidental

`mixfix` takes `Unambiguous G`. The grammar's *lexical* conditions live on `Entry`/`Grammar` as
fields (they would otherwise thread through every parse lemma), so only injectivity of `flatten`
remains as a hypothesis — and it is genuinely needed: any deterministic parser answers one tree
per token list, so two distinct trees with one flattening cannot both round-trip.

`Unambiguous` is not decidable (it quantifies over all trees). Deriving it from the lexical
fields is the open conjecture — empirically true over tens of thousands of grammars.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

open LambdaLab.Parser.IsoParser

variable {Tok : Type} [DecidableEq Tok] {G : Grammar Tok}

/-- **The general mixfix parser as an `IsoParser`.** Aligned; `print = flatten`. -/
def mixfix (hU : Unambiguous G) (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser Tok (fun _ => True) (fun t => follow e t = true)
      (Expr G e l) (Expr G e l) where
  parse input := (parseExpr e l input).map (fun z => (z.1, ⟨z.2.list, z.2.lt⟩))
  print t := (t, t.flatten)
  firstOk c rest hc := absurd trivial hc
  ok t rest hrest := by
    have h := parseExpr_complete hU t rest hrest
    simp only [runExpr] at h
    simpa [Option.map_map] using h

end LambdaLab.Parser.IsoParser.Mixfix
