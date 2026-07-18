import LambdaLab.Language1.Vernacular
import LambdaLab.IsoParser.Combinators
import LambdaLab.IsoParser.Adapters

/-!
# The vernacular biparser, derived (IsoParser)

A `Language` supplies `pTy` and `pTm` (now `IsoParser`s); the command and file parsers are derived.

**The product node without `comap`.** `IBip` built a command by giving each field a `comap` of the
shared `Command` source and threading them with `gdo`. An `IsoParser`'s value *is* its source, so
there is nothing to project: `seq` pairs the six pieces into a nested tuple, `trivialize` collapses
the (all-`PUnit`) annotation, and `imapT` reshapes the tuple into `Command` once. The keyword tokens
contribute `Unit` values that the reshape drops.

**Deferred: the character level.** `viaTokens`/`layout`/`fileParser` compose a tokenizer in front of
the token parser; that machinery is not yet ported to `IsoParser`, so this file stops at the token
level. (See the note at the bottom.)
-/

namespace LambdaLab.Language1

open LambdaLab.IsoParser

/-- An identifier: one non-keyword lexeme. -/
def pName : IsoParser Token isName (fun _ => true) Name (fun _ => PUnit) := sat isName

/-- One command: `def NAME : TYPE := BODY`. Six pieces sequenced with `seq`; the only non-trivial
seam is `ty ⟶ :=` (`FIRST(:=) ⊆ FOLLOW(ty) = {:=}`), which is the identity. -/
def Language.command (L : Language) :
    IsoParser Token (fun t => decide (t = kwDef)) followDef (Command L) (fun _ => PUnit) :=
  imapT
    (fun t => Command.decl t.2.1 t.2.2.2.1 t.2.2.2.2.2)
    (fun c => ((), c.name, (), c.ty, (), c.tm))
    (by intro t; obtain ⟨⟨⟩, n, ⟨⟩, ty, ⟨⟩, tm⟩ := t; rfl)
    (by intro c; obtain ⟨n, ty, tm⟩ := c; rfl)
    (trivialize
      (seq (tok kwDef)
        (seq pName
          (seq (tok kwColon)
            (seq L.pTy
              (seq (tok kwAssign) L.pTm (fun _ _ => rfl))
              (fun c hc => hc))
            (fun _ _ => rfl))
          (fun _ _ => rfl))
        (fun _ _ => rfl))
      (fun _ => ⟨PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit⟩)
      (by intro x a; obtain ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ := a; rfl))

/-- The all-`PUnit` `ManyAnn` — the unique inhabitant, so the parser carries *no* real annotation. -/
def dfltMany {v : Type} : (l : List v) → ManyAnn (fun _ => PUnit) l
  | []      => PUnit.unit
  | _ :: xs => ⟨PUnit.unit, dfltMany xs⟩

theorem manyAnn_uniq {v : Type} : ∀ (l : List v) (a : ManyAnn (fun _ => PUnit) l), a = dfltMany l
  | [], a => by obtain ⟨⟩ := a; rfl
  | _ :: xs, a => by obtain ⟨⟨⟩, rest⟩ := a; simp only [dfltMany]; rw [manyAnn_uniq xs rest]

/-- **The file parser**: a non-empty run of commands. A command's FIRST *is* `def` and its FOLLOW
*is* `def`, so the `many1` repetition obligation is the identity; the `ManyAnn` is `trivialize`d away
(it is all `PUnit`), so the parser is a genuine iso `stream ≃ Program`. -/
def Language.parser (L : Language) :
    IsoParser Token (fun t => decide (t = kwDef))
      (fun t => followDef t && !decide (t = kwDef)) (Program L) (fun _ => PUnit) :=
  trivialize (many1 L.command (fun _ h => h))
    (fun p => dfltMany p.toList) (fun p a => manyAnn_uniq p.toList a)

/-- **The file round-trip.** Print any program, parse it back, recover it exactly with nothing left
over — for every language, no side-conditions. -/
theorem Language.parser_roundtrip (L : Language) (prog : Program L) :
    L.parser.run (L.parser.print prog PUnit.unit) = some (⟨prog, PUnit.unit⟩, []) :=
  L.parser.run_print_nil prog PUnit.unit

/-! ## Deferred: the character level

`IBip`'s `viaTokens`/`layout`/`fileParser`/`renderProgram`/`parseFile` composed a tokenizer in front
of the token parser and carried the round-trip across both stages. That composition (`viaTokens`,
`Gap`) is not yet available for `IsoParser`; porting it is a separate piece. Until then the
vernacular round-trip lives at the token level (`parser_roundtrip`). -/

end LambdaLab.Language1
