import LambdaLab.Stlc.Named.Bridge
import LambdaLab.Stlc.Named.TypeSystem
import LambdaLab.TypeSystem.Bridged

/-!
# STLC, as the first object of `BridgedSys`

A file of its own rather than a paragraph of `Bridge.lean`, for an import-hygiene reason worth
recording: `TypeSystem/Bridged.lean` brings Mathlib's category library, whose `Quiver` arrow is
also spelled `⟶` — and `Bridge.lean` states theorems with the reduction arrow. Keeping the
Mathlib-facing object here keeps the bridge file's arrows unambiguous.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Nominal (Atom)

/-- **STLC, bridged** — one named system per atom supply, each paired with the one de Bruijn
reference; the bundled form of everything `Bridge.lean` proves. -/
def stlcBridged (N : Type) [Atom N] : TypeSystem.Bridged.Sys where
  named := { N := N, Tm := Term N, Ty := Ty }
  db := { Tm := Stlc.DeBruijn.Term, Ty := Stlc.DeBruijn.Ty }
  bridge := instTypingBridge

end LambdaLab.Stlc.Named
