import LambdaLab.Language1.Biparser
import LambdaLab.IsoParser.Adapters

/-!
# A plug-in language

The simplest possible plug-in: terms and types are each a single identifier. It exists to show
what a language author actually has to supply — and that the file parser, printer, and
round-trip proof all come back **for free**.
-/

namespace LambdaLab.Language1

open LambdaLab.IsoParser

/-- Terms and types are both a bare identifier.

`sat isName`'s real indices are FIRST = `isName`, FOLLOW = ⊤ (a single token is self-delimiting,
so anything may follow). Adapt both to what the interface asks for: `enlargeFirst` widens FIRST
up to `anyTok` (sound: `firstOk` is a negative claim); `weakenFollow` narrows FOLLOW down to the
key token (sound: the round-trip is antitone in FOLLOW). -/
def trivialLanguage : Language where
  Tm := Name
  Ty := Name
  pTy := ((sat isName).weakenFollow (fun _ _ => trivial)).enlargeFirst
    (fun _ hf => absurd trivial hf)
  pTm := ((sat isName).weakenFollow (fun _ _ => trivial)).enlargeFirst
    (fun _ hf => absurd trivial hf)

/-- `def x : A := e` — one command. -/
def prog : Program trivialLanguage :=
  (Command.decl ⟨⟨"x", by decide⟩, by decide⟩ ⟨⟨"A", by decide⟩, by decide⟩ ⟨⟨"e", by decide⟩, by decide⟩, [])

/-- Two commands. -/
def prog2 : Program trivialLanguage :=
  (Command.decl ⟨⟨"x", by decide⟩, by decide⟩ ⟨⟨"A", by decide⟩, by decide⟩ ⟨⟨"e", by decide⟩, by decide⟩,
   [Command.decl ⟨⟨"y", by decide⟩, by decide⟩ ⟨⟨"B", by decide⟩, by decide⟩ ⟨⟨"f", by decide⟩, by decide⟩])

-- printing:  ["def", "x", ":", "A", ":=", "e"]
#eval (trivialLanguage.parser.print prog).2.map (·.val)
-- and back — the leftover is `[]`, i.e. the whole file was consumed:
#eval (trivialLanguage.parser.run (trivialLanguage.parser.print prog).2).map (·.2.map (·.val))
-- the parsed names, recovered:
#eval (trivialLanguage.parser.run (trivialLanguage.parser.print prog).2).map
        (fun r => r.1.toList.map (fun c => c.name.val.val))

-- two commands round-trip too — the `many1` seam ("no further `def`") holds at end-of-input
#eval (trivialLanguage.parser.print prog2).2.map (·.val)
#eval (trivialLanguage.parser.run (trivialLanguage.parser.print prog2).2).isSome

/-- The round-trip, instantiated: **free**, inherited from the framework. -/
example (p : Program trivialLanguage) :
    trivialLanguage.parser.run (trivialLanguage.parser.print p).2
      = some ((trivialLanguage.parser.print p).1, []) :=
  trivialLanguage.parser_roundtrip p

end LambdaLab.Language1
