import LambdaLab.Abstraction.Basic
import LambdaLab.CBiparser.Indexed

/-!
# `ParserIso` — a parser as a trivial-annotation `Abs` morphism `List Tok ⇝ Tree`

The sole purpose of the parser, in the pipeline `List Char ⇝ List Token ⇝ Tree`, is to contribute an
`Abs` morphism with **trivial annotation**, to be composed with the (lossy, gaps-annotated) tokenizer.

A `ParserIso` stores just what that needs: a `flatten : Tree → List Tok` and a `parse` that is its
**left inverse** (`parse_flatten`). Storing `parse : List Tok → Option Tree` *directly* — with no
value slot for the printer to lie about — is what makes "relabeling" unrepresentable: `parse_flatten`
pins `parse (flatten t) = some t` exactly, so `parse` and `flatten` are genuine mutual inverses.

`toAbstraction` restricts the concrete side to the **image of `flatten`** (`{c // ∃ t, flatten t =
c}`), on which `abstract = parse` is a bijection with inverse `flatten`. That is an `Abs` morphism
with `Unit` annotation, and it needs only `parse_flatten` — no completeness/exactness law (parsing is
inverted on the image by the witness), and no `echo` (there is no announced value).
-/

namespace LambdaLab.Abstraction

open LambdaLab.CBiparser

private theorem get_eq {β : Type} {o : Option β} {b : β}
    (h : o.isSome) (heq : o = some b) : o.get h = b := by subst heq; rfl

/-- A parser packaged as an isomorphism onto its parseable token streams: a flattening together with
a left-inverse parser. No value slot, so no relabeling. -/
structure ParserIso (Tok Tree : Type) where
  /-- Flatten a tree to its canonical token stream. -/
  flatten : Tree → List Tok
  /-- Parse a token stream back to a tree (partial: `none` off the image). -/
  parse : List Tok → Option Tree
  /-- The round-trip law: parsing a flattening recovers the very tree. -/
  parse_flatten : ∀ t, parse (flatten t) = some t

namespace ParserIso

variable {Tok Tree : Type}

/-- `flatten` is injective — distinct trees have distinct token streams. -/
theorem flatten_inj (P : ParserIso Tok Tree) : Function.Injective P.flatten := by
  intro a b h
  have ha := P.parse_flatten a
  rw [h, P.parse_flatten b] at ha
  exact (Option.some.inj ha).symm

/-- The induced `Abs` morphism `List Tok ⇝ Tree`: `abstract = parse`, `realize = flatten`, trivial
`Unit` annotation. Concrete objects are the parseable streams (the image of `flatten`). -/
def toAbstraction (P : ParserIso Tok Tree) :
    Abstraction { c : List Tok // ∃ t, P.flatten t = c } Tree (fun _ => Unit) where
  abstract c := (P.parse c.val).get (by
      obtain ⟨t, ht⟩ := c.property; rw [← ht, P.parse_flatten]; rfl)
  realize {t} _ := ⟨P.flatten t, t, rfl⟩
  default := ()
  abstract_realize t _ := by
    have H : (P.parse (P.flatten t)).isSome := by rw [P.parse_flatten]; rfl
    rw [get_eq H (P.parse_flatten t)]
  realize_complete c := by
    refine ⟨(), Subtype.ext ?_⟩
    obtain ⟨t, ht⟩ := c.property
    have h : P.parse c.val = some t := by rw [← ht, P.parse_flatten]
    have H : (P.parse c.val).isSome := by rw [h]; rfl
    rw [get_eq H h]; exact ht

end ParserIso

/-- Build a `ParserIso` from an **aligned** `IBip` whose printer echoes its source
(`echo : (p.print t).1 = t`, `rfl` for the mixfix `ibiparser`). `flatten` is the printed token
stream, `parse` runs the biparser to end-of-input; `parse_flatten` is `IBip.roundtrip`. This is the
one place `echo` is used — the resulting `ParserIso` is relabeling-proof by construction. -/
def _root_.LambdaLab.CBiparser.IBip.toParserIso
    {α : Type} {fst fol : α → Bool} {v : Type}
    (p : IBip fst fol v v) (echo : ∀ t, (p.print t).1 = t) : ParserIso α v where
  flatten t := (p.print t).2
  parse c := (p.run c).bind (fun x => bif x.2.isEmpty then some x.1 else none)
  parse_flatten t := by
    have h : p.run (p.print t).2 = some (t, []) := by rw [p.roundtrip, echo]
    simp [h]

end LambdaLab.Abstraction
