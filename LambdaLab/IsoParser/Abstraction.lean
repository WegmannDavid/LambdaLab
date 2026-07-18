import LambdaLab.IsoParser.Basic
import LambdaLab.Abstraction.Basic

/-!
# An `IsoParser` as an `Abs` morphism `List α ⇝ v`, annotation = the parser's `Ann`

The parser's annotation family **is** the abstraction's annotation: `abstract = parse` (forgetting the
choice), `realize x a = print x a`, and the annotation over a value is exactly `Ann x` — the choices
(variable whitespace, …). Trivial `Ann` ⇒ trivial annotation. A `default` choice per value makes the
canonical reconstruction total.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Bool} {v : Type} {Ann : v → Type}

private theorem get_eq {β : Type} {o : Option β} {b : β}
    (h : o.isSome) (heq : o = some b) : o.get h = b := by subst heq; rfl

/-- **An `IsoParser` is an `Abs` morphism**, its annotation family carried straight through. `dflt`
supplies the canonical choice per value. -/
def IsoParser.toAbstraction (p : IsoParser α fst fol v Ann) (dflt : ∀ x, Ann x) :
    Abstraction { c : List α // ∃ x, ∃ a : Ann x, p.print x a = c } v Ann where
  abstract c := ((p.run c.val).get (by
      obtain ⟨x, a, hx⟩ := c.property; rw [← hx, p.run_print_nil]; rfl)).1.1
  realize {x} a := ⟨p.print x a, x, a, rfl⟩
  default {x} := dflt x
  abstract_realize x a := by
    have hr : p.run (p.print x a) = some (⟨x, a⟩, []) := p.run_print_nil x a
    have H : (p.run (p.print x a)).isSome := by rw [hr]; rfl
    rw [get_eq H hr]
  realize_complete c := by
    obtain ⟨x0, a0, hx0⟩ := c.property
    have hr : p.run c.val = some (⟨x0, a0⟩, []) := by rw [← hx0]; exact p.run_print_nil x0 a0
    have H : (p.run c.val).isSome := by rw [hr]; rfl
    have hac : ((p.run c.val).get H).1.1 = x0 := by rw [get_eq H hr]
    rw [hac]
    exact ⟨a0, Subtype.ext hx0⟩

end LambdaLab.IsoParser
