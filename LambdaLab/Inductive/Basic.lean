namespace LambdaLab.Inductive

/-- A **constructor** described as a *telescope of fields*, read left to right:
`nil` ends the constructor, `recursive` is a recursive child, `data T` is a
non-recursive field of type `T`. Field order and interleaving are preserved — e.g.
`List.cons : α → List α → List α` is `data α (recursive nil)`. -/
inductive Constructor where
| nil : Constructor
| recursive : Constructor → Constructor
| data : Type → Constructor → Constructor

/-- A **signature**: a type `Con` of constructor tags, each mapped to its field
telescope. -/
structure Signature where
  Con : Type
  constructor : Con → Constructor

/-- The arguments of a constructor `c` over a carrier `X`, read off the telescope
as a nested product: `PUnit` at `nil`, an `X` at each `recursive` field, a `T` at
each `data T` field. A **def** (not an inductive), so children are ordinary product
projections with definitional eta — no `Fin`-indexing. -/
def Constructor.Args : Constructor → Type → Type
  | .nil,            _ => PUnit
  | .recursive rest, X => X × rest.Args X
  | .data T rest,    X => T × rest.Args X

/-- One layer of `S` over `X`: pick a constructor `c`, then supply its arguments.
The action of the signature's polynomial functor. -/
def Signature.Apply (S : Signature) (X : Type) : Type :=
  Σ c : S.Con, (S.constructor c).Args X

/-- The recursive children of an arguments tuple, left to right — the `X`s sitting
at the telescope's `recursive` fields (`data` fields contribute nothing). The
relation `recursion descends along. -/
def Constructor.children {X : Type} : (c : Constructor) → c.Args X → List X
  | .nil,            _      => []
  | .recursive rest, (x, a) => x :: rest.children a
  | .data _ rest,    (_, a) => rest.children a

/-- The **immediate-child relation** induced by a destructor `d`: `x` is a
recursive child of `a` (`x ≺ a`). This is the relation generic recursion descends
along. -/
def childRel {α : Type} {S : Signature} (d : α → S.Apply α) (x a : α) : Prop :=
  x ∈ (S.constructor (d a).1).children (d a).2

/-- `α` **carries the constructors of `S`**: an algebra `construct` (build a node
from a layer) and a destructor `destruct` (the generic `casesOn` — read a value's
constructor tag and its arguments), mutually inverse so `α ≅ Apply S α`, together
with **well-foundedness of the child relation** — so generic recursion descending
to `destruct`'s children terminates.

Every concrete Lean inductive matching `S` is an instance: `construct` is its
combined constructor, `destruct` its `casesOn`; `child_wf` holds because the
children are structural subterms. -/
class Inductive (α : Type) (S : outParam Signature) where
  construct : S.Apply α → α
  destruct  : α → S.Apply α
  destruct_construct : ∀ x, destruct (construct x) = x
  construct_destruct : ∀ a, construct (destruct a) = a
  /-- The immediate-child relation `childRel destruct` is well-founded — this is
  what licenses recursion over `destruct`. -/
  child_wf : WellFounded (childRel destruct)

/-- The child relation as a `WellFoundedRelation`. With `S` explicit (no
`outParam`) this is a **def**, not a global instance, so it never shadows another
type's `WellFoundedRelation`. To recurse over a *concrete* carrier `T` with
`termination_by`/`decreasing_by`, register it once:
`instance : WellFoundedRelation T := Inductive.wfRel`. Then a function writes
`termination_by a` and discharges each call with `decreasing_by exact h`, where
`h : x ∈ … .children …` (definitionally `childRel destruct x a`). -/
@[reducible] def Inductive.wfRel {α : Type} {S : Signature} [I : Inductive α S] :
    WellFoundedRelation α := ⟨childRel I.destruct, I.child_wf⟩

/-- Well-founded recursor over any `Inductive` carrier: build `motive a` from the
`motive`-values of `a`'s recursive children, each child `x` justified by
`childRel destruct x a`. This works for **generic** `[Inductive α S]` programs
with no `WellFoundedRelation` instance in sight. -/
def Inductive.fix {α : Type} {S : Signature} [I : Inductive α S] {motive : α → Sort u}
    (F : (a : α) → ((x : α) → childRel I.destruct x a → motive x) → motive a) (a : α) :
    motive a :=
  I.child_wf.fix F a

/-- The number of constructor nodes of a value: one for the node itself, plus the
sizes of its recursive children. A generic catamorphism over any `Inductive`
carrier — each child call `size x` is justified by its membership `h` in the
node's `children` (i.e. `childRel destruct x a`). -/
def Inductive.size {α : Type} {S : Signature} [I : Inductive α S] (a : α) : Nat :=
  Inductive.fix
    (fun a rec =>
      1 + (((S.constructor (I.destruct a).1).children (I.destruct a).2).attach.map
            (fun ⟨x, h⟩ => rec x h)).sum)
    a

end LambdaLab.Inductive
