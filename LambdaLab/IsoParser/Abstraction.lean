import LambdaLab.IsoParser.Basic
import LambdaLab.Abstraction.Basic

/-!
# An `IsoParser` as a trivial-annotation `Abs` morphism `List α ⇝ v`

The pipeline interface: an `IsoParser` contributes a morphism of `Abs` with **trivial annotation**,
composable with the (lossy, gaps-annotated) tokenizer.

* `abstract = parse` — run the parser (defined on printable streams, where it succeeds fully);
* `realize  = print` — a value's canonical stream;
* concrete objects are the **printable** streams (`{c // ∃ x, print x = c}`), the image of `print`.

On that image `abstract` and `realize` are mutual inverses, so a value already pins down its stream —
the annotation is `Unit`. Because `IsoParser` bundles the iso laws, this needs no side hypothesis: the
round-trip (`run_print_nil`) alone discharges every obligation.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Bool} {v : Type}

private theorem get_eq {β : Type} {o : Option β} {b : β}
    (h : o.isSome) (heq : o = some b) : o.get h = b := by subst heq; rfl

/-- **An `IsoParser` is a trivial-annotation morphism of `Abs`.** -/
def IsoParser.toAbstraction (p : IsoParser α fst fol v) :
    Abstraction { c : List α // ∃ x, p.print x = c } v (fun _ => Unit) where
  abstract c := ((p.run c.val).get (by
      obtain ⟨x, hx⟩ := c.property; rw [← hx, p.run_print_nil]; rfl)).1
  realize {x} _ := ⟨p.print x, x, rfl⟩
  default := ()
  abstract_realize x _ := by
    have hr : p.run (p.print x) = some (x, []) := p.run_print_nil x
    have H : (p.run (p.print x)).isSome := by rw [hr]; rfl
    rw [get_eq H hr]
  realize_complete c := by
    refine ⟨(), Subtype.ext ?_⟩
    obtain ⟨x, hx⟩ := c.property
    have hr : p.run c.val = some (x, []) := by rw [← hx]; exact p.run_print_nil x
    have H : (p.run c.val).isSome := by rw [hr]; rfl
    rw [show ((p.run c.val).get H).1 = x from congrArg Prod.fst (get_eq H hr)]
    exact hx

end LambdaLab.IsoParser
