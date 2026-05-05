import LambdaLab.Parser.Mixfix.Basic

/-!
# Mixfix parse trees

A `Tree α` is a parse tree. Its leaves are atoms (identifier-like
tokens); its internal nodes are operators applied to a heterogeneous
child list — a `Tree α` per `recurse` hole and a `β` value per
`sub p` hole (where `β` is the sub-parser's carrier).

Because the children's types depend on the operator's holes, `Tree` and
the child-list type `Children` are defined by mutual induction:

```
inductive Tree (α : Type) : Type 1 where
  | atom : String → Tree α
  | node : (op : Operator α) → Children α op.holes → Tree α

inductive Children (α : Type) : List (HoleSpec α) → Type 1 where
  | nil
  | consRec : Tree α → Children α hs → Children α (.recurse :: hs)
  | consSub : β → Children α hs → Children α (.sub p :: hs)
```

Two operations:

* `Tree.flatten` — token stream of a tree. Recursive holes use
  `Tree.flatten`; sub holes use the corresponding `p.printer`.
* `Tree.eval`    — interpret a tree to produce an `α`, threading the
  curried `buildType α holes` through the heterogeneous child list.
-/

namespace LambdaLab.Parser.Mixfix

/-! ## Parse trees and child lists -/

mutual
  /-- A mixfix parse tree producing values of type `α`. The `app` case
  represents juxtaposition (function application by adjacency); it
  carries its own combiner so `eval` doesn't need to consult the
  grammar. -/
  inductive Tree (α : Type) : Type 1 where
    | atom : String → Tree α
    | node : (op : Operator α) → Children α op.holes → Tree α
    | app  : (α → α → α) → Tree α → Tree α → Tree α

  /-- A heterogeneous list of children matching a list of hole specs:
  a `Tree α` per recursive hole, and a `β` value per sub hole. -/
  inductive Children (α : Type) : List (HoleSpec α) → Type 1 where
    | nil : Children α []
    | consRec {hs : List (HoleSpec α)} :
        Tree α → Children α hs → Children α (.recurse :: hs)
    | consSub {β : Type} {p : Parser β} {hs : List (HoleSpec α)} :
        β → Children α hs → Children α (.sub p :: hs)
end

/-! ## Flattening: tree → token stream

The four fixities determine how the operator's name-parts and the
flattened sub-pieces interleave; the `weave*` helpers capture each
pattern.
-/

def weaveClosed : List String → List (List String) → List String
  | [],          _        => []
  | [p],         _        => [p]
  | p :: _ :: _, []       => [p]
  | p :: ps,     c :: cs  => p :: c ++ weaveClosed ps cs

def weavePrefix : List String → List (List String) → List String
  | [],          _        => []
  | _ :: _,      []       => []
  | p :: ps,     c :: cs  => p :: c ++ weavePrefix ps cs

def weavePostfix : List String → List (List String) → List String
  | [],          _        => []
  | _ :: _,      []       => []
  | p :: ps,     c :: cs  => c ++ p :: weavePostfix ps cs

def weaveInfix : List String → List (List String) → List String
  | [],          []       => []
  | [],          [c]      => c
  | [],          _ :: _   => []
  | _ :: _,      []       => []
  | p :: ps,     c :: cs  => c ++ p :: weaveInfix ps cs

mutual
  /-- Flatten a parse tree into its token stream. -/
  def Tree.flatten {α : Type} : Tree α → List String
    | .atom s     => [s]
    | .node op cs =>
        let parts := Children.flatten cs
        match op.fixity with
        | .closed   => weaveClosed   op.nameParts parts
        | .prefix   => weavePrefix   op.nameParts parts
        | .postfix  => weavePostfix  op.nameParts parts
        | .infix _  => weaveInfix    op.nameParts parts
    | .app _ a b  => Tree.flatten a ++ Tree.flatten b
  termination_by t => sizeOf t

  /-- Flatten a child list. Recursive children call back into
  `Tree.flatten`; sub children use their bundled parser's `printer`. -/
  def Children.flatten {α : Type} :
      ∀ {hs : List (HoleSpec α)}, Children α hs → List (List String)
    | _, .nil                     => []
    | _, .consRec t cs            => Tree.flatten t :: Children.flatten cs
    | _, .consSub (p := p) v cs   => p.printer v :: Children.flatten cs
  termination_by _ cs => sizeOf cs
end

/-! ## Evaluation: tree → α -/

mutual
  /-- Evaluate a parse tree using the grammar's `atomBuild` for atoms,
  the operators' `build` functions for nodes, and the per-node `app`
  combiner for juxtaposition. -/
  def Tree.eval {α : Type} (g : Grammar α) : Tree α → α
    | .atom s     => g.atomBuild s
    | .node op cs => Children.evalApply g op.build cs
    | .app f a b  => f (Tree.eval g a) (Tree.eval g b)
  termination_by t => sizeOf t

  /-- Apply a curried build function to the values evaluated from a
  child list, threading recursive holes through `Tree.eval` and passing
  sub-hole values straight through. -/
  def Children.evalApply {α : Type} (g : Grammar α) :
      ∀ {hs : List (HoleSpec α)}, buildType α hs → Children α hs → α
    | [],     a, .nil          => a
    | _ :: _, f, .consRec t cs => Children.evalApply g (f (Tree.eval g t)) cs
    | _ :: _, f, .consSub v cs => Children.evalApply g (f v) cs
  termination_by _ _ cs => sizeOf cs
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (
          rename_i tail
          calc sizeOf t
              < sizeOf t + 1 := Nat.lt_succ_self _
            _ ≤ 1 + sizeOf tail + sizeOf t + sizeOf cs := by omega
        )
end

end LambdaLab.Parser.Mixfix
