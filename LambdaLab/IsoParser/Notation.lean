import LambdaLab.IsoParser.Combinators

/-!
# `gdo` — applicative sequencing sugar for `IsoParser`

`IsoParser` is an *iso*, so any reshape of the value needs `imapT` (both directions). But the
plumbing around it — right-nesting `seq`, discharging each seam, and collapsing the `PUnit`
annotations `seq` leaves behind — is mechanical. `gdo` does exactly that:

```
gdo p₁ p₂ … pₙ   ≡   trivializeSub (seq p₁ (seq p₂ (… pₙ) (by iso_seam)) (by iso_seam))
```

The result's value is the nested tuple `(v₁ × v₂ × … × vₙ)` with the trivial annotation; reshape it
into your record with `imapT`.
-/

namespace LambdaLab.IsoParser

/-- Products of subsingletons are subsingletons — so `seq`'s nested-`PUnit` annotations collapse. -/
instance instSubsingletonProd {a b : Type} [Subsingleton a] [Subsingleton b] :
    Subsingleton (a × b) :=
  ⟨fun _ _ => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

variable {α : Type} {fst fol : α → Bool} {v : Type} {Ann : v → Type}

/-- **Collapse a uniquely-determined (subsingleton) annotation to `PUnit`** — the typeclass version
of `trivialize`, with no manual default/uniqueness proof. -/
def trivializeSub (p : IsoParser α fst fol v Ann)
    [∀ x, Inhabited (Ann x)] [∀ x, Subsingleton (Ann x)] :
    IsoParser α fst fol v (fun _ => PUnit) :=
  trivialize p (fun _ => default) (fun _ a => Subsingleton.elim a default)

/-- Discharge a `seq` seam `∀ c, FIRST₂ c → FOLLOW₁ c`. Trivial when FOLLOW₁ = ⊤ (`rfl`) or when it
*is* FIRST₂ (`exact ha`); bring any extra lexical fact into scope with `have` before the block. -/
macro "iso_seam" : tactic =>
  `(tactic| (intro a ha; first | rfl | exact ha | assumption | simp_all | decide))

open Lean in
/-- Applicative sequencing: right-nest `seq`, discharge each seam with `iso_seam`, and
`trivializeSub` the annotation. Value is the nested tuple `(v₁ × v₂ × … × vₙ)`. -/
syntax "gdo " (ppSpace colGt term:max)+ : term

open Lean in
macro_rules
  | `(gdo $ps:term*) => do
      let n := ps.size
      let mut acc : TSyntax `term := ps[n-1]!
      for i in [0:n-1] do
        acc ← `(seq $(ps[n-2-i]!) $acc (by iso_seam))
      `(trivializeSub $acc)

/-! ## Dropping a `Unit`-valued neighbour — the applicative `<~` / `~>`

`Unit`-valued pieces (tokens) carry no information, and printing re-emits them, so they can be
dropped from the value *invertibly*. `p <~ q` keeps `p`'s value and drops `q` (which must be
`Unit`-valued); `p ~> q` keeps `q` and drops `p`. This is how you get `(a, b)` with no `Unit` in the
middle: `a-parser` `seq` (`= token ~> b-parser`). -/

/-- Sequence, **keeping the left** value; `q` (a `Unit`-valued piece, e.g. a token) is dropped. -/
def seqL {f1 fo1 f2 fo2 : α → Bool} {a : Type}
    (p : IsoParser α f1 fo1 a (fun _ => PUnit)) (q : IsoParser α f2 fo2 Unit (fun _ => PUnit))
    (hseam : ∀ c, f2 c = true → fo1 c = true) : IsoParser α f1 fo2 a (fun _ => PUnit) :=
  imapT (fun x => x.1) (fun y => (y, ()))
    (by intro x; obtain ⟨_, ⟨⟩⟩ := x; rfl) (by intro _; rfl)
    (trivializeSub (seq p q hseam))

/-- Sequence, **keeping the right** value; `p` (a `Unit`-valued piece, e.g. a token) is dropped. -/
def seqR {f1 fo1 f2 fo2 : α → Bool} {b : Type}
    (p : IsoParser α f1 fo1 Unit (fun _ => PUnit)) (q : IsoParser α f2 fo2 b (fun _ => PUnit))
    (hseam : ∀ c, f2 c = true → fo1 c = true) : IsoParser α f1 fo2 b (fun _ => PUnit) :=
  imapT (fun x => x.2) (fun y => ((), y))
    (by intro x; obtain ⟨⟨⟩, _⟩ := x; rfl) (by intro _; rfl)
    (trivializeSub (seq p q hseam))

notation:65 l:66 " <~ " r:66 => seqL l r (by iso_seam)
notation:65 l:66 " ~> " r:66 => seqR l r (by iso_seam)

end LambdaLab.IsoParser
