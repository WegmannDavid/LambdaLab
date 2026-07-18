import LambdaLab.IsoParser.Basic

/-!
# Plug-in boundary adapters: `weakenFollow` / `enlargeFirst`

The two direction-sound index adjustments an `IsoParser` admits, and exactly what a language needs
to fit its parser to a fixed interface (`IsoParser α anyTok followKey …`):

* **`weakenFollow`** — narrow FOLLOW. The round-trip law is *antitone* in FOLLOW (a smaller FOLLOW
  admits fewer continuations, a weaker claim), discharged through `HeadIn.mono`.
* **`enlargeFirst`** — widen FIRST. `firstOk` is *negative* ("outside FIRST, I fail"), so a larger
  FIRST promises less; widening all the way to `anyTok` makes it vacuous.

There is no `comap`/indexed-`bind` here: an `IsoParser`'s value *is* its source (an iso), so a
product node is built by `seq` (pairing values) then `imapT` (reshaping the tuple), not by
projecting a shared source per field.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Bool} {v : Type} {Ann : v → Type}

/-- **Narrow the FOLLOW.** Sound because the round-trip is antitone in FOLLOW. -/
def IsoParser.weakenFollow {fol' : α → Bool} (h : ∀ c, fol' c = true → fol c = true)
    (p : IsoParser α fst fol v Ann) : IsoParser α fst fol' v Ann where
  parse := p.parse
  print := p.print
  firstOk := p.firstOk
  parse_print x a rest hr := p.parse_print x a rest (hr.mono h)
  print_parse := p.print_parse

/-- **Widen the FIRST.** Sound because `firstOk` is a negative claim; widening to `anyTok` makes it
vacuous. -/
def IsoParser.enlargeFirst {fst' : α → Bool} (h : ∀ c, fst' c = false → fst c = false)
    (p : IsoParser α fst fol v Ann) : IsoParser α fst' fol v Ann where
  parse := p.parse
  print := p.print
  firstOk c rest hc := p.firstOk c rest (h c hc)
  parse_print := p.parse_print
  print_parse := p.print_parse

end LambdaLab.IsoParser
