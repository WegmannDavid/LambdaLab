import LambdaLab.IsoParser.Basic

/-!
# Plug-in boundary adapters: `weakenFollow` / `enlargeFirst`

The two direction-sound index adjustments an `IsoParser` admits — what a language needs to fit
its parser to a fixed interface (`IsoParser α anyTok followKey …`):

* **`weakenFollow`** — narrow FOLLOW. The round-trip law is *antitone* in FOLLOW (a smaller FOLLOW
  admits fewer continuations, a weaker claim), discharged through `HeadIn.mono`.
* **`enlargeFirst`** — widen FIRST. `firstOk` is *negative* ("outside FIRST, I fail"), so a larger
  FIRST promises less; widening all the way to `⊤` makes it vacuous.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Prop} {w v : Type}

/-- **Narrow the FOLLOW.** Sound because the round-trip is antitone in FOLLOW. -/
def IsoParser.weakenFollow {fol' : α → Prop} (h : ∀ c, fol' c → fol c)
    (p : IsoParser α fst fol w v) : IsoParser α fst fol' w v where
  parse := p.parse
  print := p.print
  firstOk := p.firstOk
  ok a rest hr := p.ok a rest (hr.mono h)

/-- **Widen the FIRST.** Sound because `firstOk` is a negative claim; widening to `⊤` makes it
vacuous. -/
def IsoParser.enlargeFirst {fst' : α → Prop} (h : ∀ c, ¬ fst' c → ¬ fst c)
    (p : IsoParser α fst fol w v) : IsoParser α fst' fol w v where
  parse := p.parse
  print := p.print
  firstOk c rest hc := p.firstOk c rest (h c hc)
  ok := p.ok

end LambdaLab.IsoParser
