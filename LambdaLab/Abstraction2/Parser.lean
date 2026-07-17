import LambdaLab.Abstraction2.Basic

/-!
# The parser abstraction: `abstract = parse`, `realize = flatten`

A parser `parse : List Tok → Tree` is the **lossy forward** map (token string ↦ its tree); `flatten :
Tree → List Tok` reconstructs the canonical string. This is an `Abs` morphism `List Tok ⇝ Tree`:

* `abstract = parse`   — parse the token string,
* `realize  = flatten` — flatten a tree back to its canonical token string.

The two laws are exactly the two halves of the round-trip:

* `abstract_realize` = `parse (flatten t) = t` — the biparser **round-trip / soundness** law (the
  string a tree prints to parses back to that tree). This is the one assumption.
* `realize_complete` follows from it on the concrete side: every **printable** string `c = flatten t`
  satisfies `flatten (parse c) = flatten (parse (flatten t)) = flatten t = c`.

So the concrete objects are restricted to printable strings — a string that is no tree's printout is
not in scope. On those, `parse` and `flatten` are mutually inverse, hence the **annotation is
trivial** (`Unit`): a tree already pins down its canonical string, leaving nothing to annotate. The
abstraction records precisely that `parse` is a retraction of `flatten`.
-/

namespace LambdaLab.Abstraction2

/-- The parser abstraction `List Tok ⇝ Tree` for a parser `parse` with right inverse `flatten`
(`roundtrip : parse (flatten t) = t`): `abstract = parse`, `realize = flatten`, trivial annotation.
Computable — no choice. -/
def parseAbstraction {Tok Tree : Type}
    (parse : List Tok → Tree) (flatten : Tree → List Tok)
    (roundtrip : ∀ t, parse (flatten t) = t) :
    Abstraction { c : List Tok // ∃ t, flatten t = c } Tree (fun _ => Unit) where
  abstract c := parse c.val
  realize {t} _ := ⟨flatten t, t, rfl⟩
  default := ()
  abstract_realize t _ := roundtrip t
  realize_complete := fun c => ⟨(), Subtype.ext <| by
    obtain ⟨t, ht⟩ := c.2; rw [← ht]; exact congrArg flatten (roundtrip t)⟩

end LambdaLab.Abstraction2
