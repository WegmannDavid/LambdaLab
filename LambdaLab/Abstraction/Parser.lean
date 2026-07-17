import LambdaLab.Abstraction.Basic
import LambdaLab.CBiparser.Indexed

/-!
# The parser abstraction from an `IBip`: `abstract = parse`, `realize = flatten`

An **aligned** biparser (source and value the same type `v`) is exactly a parser packaged with its
reconstruction: `p.print t = (t, flatten t)` and `p.run` parses. Its `IBip.roundtrip` law says
`parse (flatten t) = t`, so it is an `Abs` morphism `List α ⇝ v`:

* `abstract = parse`   — run the biparser (defined on printable strings, where it always succeeds),
* `realize  = flatten` — a value's canonical token string, `(p.print ·).2`.

The concrete objects are the **printable** strings `{c // ∃ t, (p.print t).2 = c}`; a string that is
no value's printout is out of scope. On those, `parse` and `flatten` are mutually inverse, so a value
already pins down its canonical string — the **annotation is trivial** (`Unit`).

The one thing `IBip` alone does not give is that the printer *echoes* its parsed value as its source
(`(p.print t).1 = t`); that is what turns the round-trip `parse (flatten t) = (p.print t).1` into
`parse (flatten t) = t`. It holds `rfl` for any aligned printer of the form `t ↦ (t, flatten t)`
(e.g. the mixfix `ibiparser`), and is the `echo` hypothesis below.
-/

namespace LambdaLab.Abstraction

open Classical LambdaLab.CBiparser

private theorem get_eq {β : Type} {o : Option β} {b : β}
    (h : o.isSome) (heq : o = some b) : o.get h = b := by subst heq; rfl

/-- The parser abstraction `List α ⇝ v` induced by an aligned `IBip` whose printer echoes its source
(`echo : (p.print t).1 = t`): `abstract = parse` (run the biparser), `realize = flatten`
(`(p.print ·).2`), trivial annotation. Computable. -/
def _root_.LambdaLab.CBiparser.IBip.parserAbstraction
    {α : Type} {fst fol : α → Bool} {v : Type}
    (p : IBip fst fol v v) (echo : ∀ t, (p.print t).1 = t) :
    Abstraction { c : List α // ∃ t, (p.print t).2 = c } v (fun _ => Unit) where
  abstract c := ((p.run c.val).get (by
      obtain ⟨t, ht⟩ := c.property; rw [← ht, p.roundtrip]; rfl)).1
  realize {t} _ := ⟨(p.print t).2, t, rfl⟩
  default := ()
  abstract_realize t _ := by
    have hr : p.run (p.print t).2 = some (t, []) := by rw [p.roundtrip, echo]
    have H : (p.run (p.print t).2).isSome := by rw [hr]; rfl
    rw [get_eq H hr]
  realize_complete c := by
    refine ⟨(), Subtype.ext ?_⟩
    obtain ⟨t₀, ht₀⟩ := c.property
    have hrun : p.run c.val = some (t₀, []) := by rw [← ht₀, p.roundtrip, echo]
    have H : (p.run c.val).isSome := by rw [hrun]; rfl
    rw [congrArg Prod.fst (get_eq H hrun)]
    exact ht₀

end LambdaLab.Abstraction
