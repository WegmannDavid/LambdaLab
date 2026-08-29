import LambdaLab.Parser.IsoParser.Mixfix.Exact

/-!
# The general mixfix `IsoParser`

Packages the self-contained mixfix parser as an `IsoParser` over the abstract token alphabet.
**Aligned**: source = value = the tree, `print` is `flatten`.

* **FIRST = ⊤** (`firstOk` vacuous) — exactly what `Language`'s interface asks for.
* **FOLLOW** carries the content: the computed `follow` (`Complete.lean`) — tokens at which the
  greedy parser provably stops.
* **`ok`** is *derived* (`parseExpr_complete`, `Exact.lean`) from the decomposition set out in
  `Complete.lean`.

## No hypotheses

`mixfix` takes none. Unambiguity — injectivity of `flatten`, which any deterministic parser needs
— used to be a hypothesis; it is now a theorem (`Unambiguity.unambiguous`), derived from the
grammar's own lexical fields (`headsDistinct`, `varDisjoint`, `juxtUnique`, `interiorTerminates`),
which live on `Entry`/`Grammar` precisely so that they do not thread through every parse lemma.
So a `Grammar` is round-tripping by construction.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

open LambdaLab.Parser.IsoParser

variable {Tok : Type} [DecidableEq Tok] {G : Grammar Tok}

/-- **The general mixfix parser as an `IsoParser`.** Aligned; `print = flatten`. -/
def mixfix (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser Tok (fun _ => True) (fun t => follow e t = true)
      (Expr G e l) (Expr G e l) where
  parse input := (parseExpr e l input).map (fun z => (z.1, ⟨z.2.list, z.2.lt⟩))
  print t := (t, t.flatten)
  firstOk c rest hc := absurd trivial hc
  ok t rest hrest := by
    have h := parseExpr_complete t rest hrest
    simp only [runExpr] at h
    simpa [Option.map_map] using h

/-- **The mixfix parser is exact** — `parseExpr_sound` repackaged: the parser is aligned, so the
tree it returns is itself the source whose print (`flatten`) is the consumed input. -/
theorem mixfix_exact (e : G.Ent) (l : Level (G.entry e)) : (mixfix e l).Exact := by
  intro input b rest h
  obtain ⟨r, hp, hv⟩ := run_eq_some h
  refine ⟨b, rfl, ?_⟩
  have hp' : (parseExpr e l input).map
      (fun z => (z.1, (⟨z.2.list, z.2.lt⟩ : { r : List Tok // r.length < input.length })))
      = some (b, r) := hp
  cases hq : parseExpr e l input with
  | none => rw [hq] at hp'; simp at hp'
  | some z =>
      rw [hq] at hp'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨hb, hr⟩ := hp'
      subst hb
      have hs := parseExpr_sound e l input z.1 z.2 hq
      rw [← hv, ← hr]
      exact hs

end LambdaLab.Parser.IsoParser.Mixfix
