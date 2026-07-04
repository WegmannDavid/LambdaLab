import LambdaLab.Parser1.Mixfix.Tree

/-!
# Rendering: `Expr` → `List Char`, driven by a `Policy`

`Layout` and `Policy` (moved here from `Biparse`) describe how to lay out a tree;
`renderExpr` walks the tree, threading the policy's `State` top-down through
`traverse` and emitting the chosen separators — nonempty `NESep` between the parts
of every operator body, and the global `pre`/`post` once at the outermost call.
-/

namespace LambdaLab.Parser1.Mixfix

open LambdaLab.Parser1

/-- The rendering **telescope** for an operator body `ps`, threaded left-to-right.
The leading edge is a possibly-empty separator run; then, for each part, a `State`
to render it with and a **continuation fed that part's rendered chars** — so the
next step (its gap, the next state) can depend on what the previous part rendered
to (e.g. advance a cursor by its length).

Indexed by the body `ps` (`= Operator.body e o`), so it lines up part-for-part with
`Parts G ps`, which the renderer walks in lockstep.

`Layout [hole, namePart "+", hole]` (`x + y`) unfolds to exactly
`List Sep × State × (List Char → NESep × State × (List Char → NESep × State ×
(List Char → List Sep × State)))` — possibly-empty outer edges, nonempty internal
gaps. -/
def LayoutTail (G : Grammar) (State : Type) : List (Part G) → Type
  | []      => List (Sep G) × State
  | _ :: ps => NESep G × State × (List Char → LayoutTail G State ps)

/-- The full telescope: like `LayoutTail` but the first separator (before the first
part) is the possibly-empty **left edge**. -/
def Layout (G : Grammar) (State : Type) : List (Part G) → Type
  | []      => List (Sep G) × State
  | _ :: ps => List (Sep G) × State × (List Char → LayoutTail G State ps)

/-- The uniform tail: empty right edge, every gap `sep`, the constant state `st` at
every part (continuations ignore the rendered chars). -/
def LayoutTail.const {G : Grammar} {State : Type} (sep : NESep G) (st : State) :
    (ps : List (Part G)) → LayoutTail G State ps
  | []      => ([], st)
  | _ :: ps => (sep, st, fun _ => LayoutTail.const sep st ps)

/-- The uniform telescope: empty left/right edges, every internal gap `sep`, the
constant state `st` everywhere. The building block for a stateless single-separator
policy. -/
def Layout.const {G : Grammar} {State : Type} (sep : NESep G) (st : State) :
    (ps : List (Part G)) → Layout G State ps
  | []      => ([], st)
  | _ :: ps => ([], st, fun _ => LayoutTail.const sep st ps)

/-- A rendering **policy**: a user-chosen `State`, an `initial` state, and a
`traverse` that lays out an operator node's body as the state-threading telescope
above. Internal gaps are typed `NESep` (nonempty — so every render re-parses); only
the two outer edges are the possibly-empty `List (Sep G)`. -/
structure Policy (G : Grammar) where
  State    : Type
  initial  : State
  traverse : (e : G.Ent) → (o : (G.entry e).Op) → State →
    Layout G State (Operator.body e o)
  /-- For a variable leaf: its possibly-empty left and right separator edges. These
  are nonempty only when the leaf is the whole (top) tree — an *inner* leaf returns
  `([], [])`, since the parent's telescope gaps already surround it. This is what
  lets `render_complete`'s cursor witness reproduce a bare-variable input like
  `"  x  "`. -/
  traverseVar : (e : G.Ent) → Token G.isSep → State → List (Sep G) × List (Sep G)

mutual
  /-- Render a tree at state `state`. An operator node lays out its body with
  `traverse`; a variable leaf gets its edges from `traverseVar`. -/
  def Expr.render {G : Grammar} (policy : Policy G) (state : policy.State) (e : G.Ent)
      {l : Level (G.entry e)} : Expr G e l → List Char
    | .op o _ parts => Parts.render policy (Operator.body e o) (policy.traverse e o state) parts
    | .var t _      =>
        let (leftEdge, rightEdge) := policy.traverseVar e t state
        leftEdge.map (·.val) ++ t.val.toList ++ rightEdge.map (·.val)

  /-- Render a body from its first part: emit the left edge, render the part with
  its state, feed the rendered chars into the continuation, and continue. -/
  def Parts.render {G : Grammar} (policy : Policy G) :
      (ps : List (Part G)) → Layout G policy.State ps → Parts G ps → List Char
    | [],                    layout,            _                 => (layout.1).map (·.val)
    | .namePart _ :: psTail, (leftEdge, _, k),  .namePart tk prest =>
        let r := tk.val.toList
        leftEdge.map (·.val) ++ r ++ Parts.renderTail policy psTail (k r) prest
    | .hole e' _ :: psTail,  (leftEdge, st, k), .hole ex prest =>
        let r := Expr.render policy st e' ex
        leftEdge.map (·.val) ++ r ++ Parts.renderTail policy psTail (k r) prest

  /-- Render the remaining parts: each gap is a nonempty `NESep`; the final step is
  the possibly-empty right edge. -/
  def Parts.renderTail {G : Grammar} (policy : Policy G) :
      (ps : List (Part G)) → LayoutTail G policy.State ps → Parts G ps → List Char
    | [],                    layout,        _                 => (layout.1).map (·.val)
    | .namePart _ :: psTail, (gap, _, k),   .namePart tk prest =>
        let r := tk.val.toList
        gap.toChars ++ r ++ Parts.renderTail policy psTail (k r) prest
    | .hole e' _ :: psTail,  (gap, st, k),  .hole ex prest =>
        let r := Expr.render policy st e' ex
        gap.toChars ++ r ++ Parts.renderTail policy psTail (k r) prest
end

/-- Top-level render for a loosest tree: render it under `policy.initial`. Any
global leading/trailing whitespace is the top node's own edges (an op's
`traverse` left/right, or a var's `traverseVar`). This is the `Renderer` fed to the
`Biparser`. -/
def renderExpr {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (policy : Policy G) : List Char :=
  Expr.render policy policy.initial e ex

end LambdaLab.Parser1.Mixfix
