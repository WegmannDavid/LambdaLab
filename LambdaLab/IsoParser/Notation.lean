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

end LambdaLab.IsoParser
