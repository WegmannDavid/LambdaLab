import LambdaLab.Language1.Biparser

/-!
# A plug-in language

The simplest possible plug-in: terms and types are each a single identifier. It exists to show
what a language author actually has to supply — and that the file parser, printer, and round-trip
proof all come back **for free**.
-/

namespace LambdaLab.Language1

open LambdaLab.IsoParser

/-- Terms and types are both a bare identifier.

Everything a language must provide is here: the two parsers and their boundary adapters. `sat
isName`'s real indices are FIRST = `isName`, FOLLOW = ⊤ (a single token is self-delimiting):
`enlargeFirst` widens FIRST up to `anyTok`, `weakenFollow` narrows FOLLOW to the key token. -/
def trivialLanguage : Language where
  Tm := Name
  Ty := Name
  pTy := ((sat isName).weakenFollow (fun _ _ => rfl)).enlargeFirst (fun _ hf => by simp at hf)
  pTm := ((sat isName).weakenFollow (fun _ _ => rfl)).enlargeFirst (fun _ hf => by simp at hf)

/-- `def x : A := e` — one command. -/
def prog : Program trivialLanguage :=
  (Command.decl ⟨⟨"x", by decide⟩, by decide⟩ ⟨⟨"A", by decide⟩, by decide⟩ ⟨⟨"e", by decide⟩, by decide⟩, [])

/-- Two commands. -/
def prog2 : Program trivialLanguage :=
  (Command.decl ⟨⟨"x", by decide⟩, by decide⟩ ⟨⟨"A", by decide⟩, by decide⟩ ⟨⟨"e", by decide⟩, by decide⟩,
   [Command.decl ⟨⟨"y", by decide⟩, by decide⟩ ⟨⟨"B", by decide⟩, by decide⟩ ⟨⟨"f", by decide⟩, by decide⟩])

-- printing:  ["def", "x", ":", "A", ":=", "e"]
#eval (trivialLanguage.parser.print prog PUnit.unit).map (·.val)
-- and back — the leftover is `[]`, i.e. the whole file was consumed:
#eval (trivialLanguage.parser.run (trivialLanguage.parser.print prog PUnit.unit)).map (·.2.map (·.val))
-- the parsed names, recovered:
#eval (trivialLanguage.parser.run (trivialLanguage.parser.print prog PUnit.unit)).map
        (fun r => r.1.1.toList.map (fun c => c.name.val.val))

-- two commands round-trip too — the `many1` seam ("no further `def`") holds at end-of-input
#eval (trivialLanguage.parser.print prog2 PUnit.unit).map (·.val)
#eval (trivialLanguage.parser.run (trivialLanguage.parser.print prog2 PUnit.unit)).isSome

/-- The round-trip, instantiated: **free**, inherited from the framework. -/
example (p : Program trivialLanguage) :
    trivialLanguage.parser.run (trivialLanguage.parser.print p PUnit.unit)
      = some (⟨p, PUnit.unit⟩, []) :=
  trivialLanguage.parser_roundtrip p

end LambdaLab.Language1
