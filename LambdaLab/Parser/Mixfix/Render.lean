import LambdaLab.Parser.Mixfix.Tree

/-!
# Rendering: `Expr` → `List Char`, driven by a `Policy`

`Layout` and `Policy` (moved here from `Biparse`) describe how to lay out a tree;
`renderExpr` walks the tree, threading the policy's `State` top-down through
`traverse` and emitting the chosen separators — nonempty `NESep` between the parts
of every operator body, and the global `pre`/`post` once at the outermost call.
-/

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

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
  | []      => State
  | _ :: ps => NESep G × State × (State → List Char → LayoutTail G State ps)

/-- The full telescope: like `LayoutTail` but the first separator (before the first
part) is the possibly-empty **left edge**. There is no right edge: the separators
after a part are always the *next* part's gap (single owner), and the very last
trailing run is the global `Policy.trail`.

Each continuation is fed **two** things: the `State` *after* the previous part
(threaded by actual consumption — a token's `step`, or a hole subtree's own return),
and the previous part's **rendered chars** (for output-driven layout choices). The
two concerns are separate, so state threading never depends on rendered length. -/
def Layout (G : Grammar) (State : Type) : List (Part G) → Type
  | []      => State
  | _ :: ps => List (Sep G) × State × (State → List Char → LayoutTail G State ps)

/-- The uniform tail: every gap `sep`, the constant state `st` at every part
(continuations ignore both the threaded state and the rendered chars). -/
def LayoutTail.const {G : Grammar} {State : Type} (sep : NESep G) (st : State) :
    (ps : List (Part G)) → LayoutTail G State ps
  | []      => st
  | _ :: ps => (sep, st, fun _ _ => LayoutTail.const sep st ps)

/-- The uniform telescope: empty left edge, every internal gap `sep`, the constant
state `st` everywhere. The building block for a stateless single-separator policy. -/
def Layout.const {G : Grammar} {State : Type} (sep : NESep G) (st : State) :
    (ps : List (Part G)) → Layout G State ps
  | []      => st
  | _ :: ps => ([], st, fun _ _ => LayoutTail.const sep st ps)

/-- A rendering **policy**: a user-chosen `State`, an `initial` state, and a
`traverse` that lays out an operator node's body as the state-threading telescope
above. Internal gaps are typed `NESep` (nonempty — so every render re-parses); the
left edge is the possibly-empty `List (Sep G)`. Every separator run has a single
owner (a token's leading gap), so nothing is double-counted. -/
structure Policy (G : Grammar) where
  State    : Type
  initial  : State
  /-- Advance the state past a rendered **name-part token** (the input it consumes). -/
  step     : State → Token G.isSep → State
  traverse : (e : G.Ent) → (o : (G.entry e).Op) → State →
    Layout G State (Operator.body e o)
  /-- For a variable leaf: its possibly-empty **leading** separator run, and the
  state after emitting the leaf. The leading run is nonempty only when the leaf
  begins the whole output; an inner leaf gets `[]` (the parent's gap already leads
  into it). There is no trailing edge — the separators after a token are the next
  token's gap, or the global `trail`. -/
  traverseVar : (e : G.Ent) → Token G.isSep → State → List (Sep G) × State
  /-- The global trailing separator run, emitted once after the whole tree. -/
  trail : State → List (Sep G)

mutual
  /-- Render a tree at state `state`, returning the chars and the state afterwards.
  An operator node lays out its body with `traverse`; a variable leaf gets its
  leading edge and next state from `traverseVar`. -/
  def Expr.render {G : Grammar} (policy : Policy G) (state : policy.State) (e : G.Ent)
      {l : Level (G.entry e)} : Expr G e l → List Char × policy.State
    | .op o _ parts => Parts.render policy (Operator.body e o) (policy.traverse e o state) parts
    | .var t _      =>
        let (leftEdge, state') := policy.traverseVar e t state
        (leftEdge.map (·.val) ++ t.val.toList, state')

  /-- Render a body from its first part: emit the left edge, render the part, feed
  the state **after** it (a token's `step`, or the hole subtree's own returned state)
  and its rendered chars into the continuation, and continue. -/
  def Parts.render {G : Grammar} (policy : Policy G) :
      (ps : List (Part G)) → Layout G policy.State ps → Parts G ps →
      List Char × policy.State
    | [],                    st,                _                 => ([], st)
    | .namePart _ :: psTail, (leftEdge, st, k), .namePart tk prest =>
        let r := tk.val.toList
        let (rest, st') := Parts.renderTail policy psTail (k (policy.step st tk) r) prest
        (leftEdge.map (·.val) ++ r ++ rest, st')
    | .hole e' _ :: psTail,  (leftEdge, st, k), .hole ex prest =>
        let (r, stAfter) := Expr.render policy st e' ex
        let (rest, st') := Parts.renderTail policy psTail (k stAfter r) prest
        (leftEdge.map (·.val) ++ r ++ rest, st')

  /-- Render the remaining parts: each gap is a nonempty `NESep`. -/
  def Parts.renderTail {G : Grammar} (policy : Policy G) :
      (ps : List (Part G)) → LayoutTail G policy.State ps → Parts G ps →
      List Char × policy.State
    | [],                    st,            _                 => ([], st)
    | .namePart _ :: psTail, (gap, st, k),  .namePart tk prest =>
        let r := tk.val.toList
        let (rest, st') := Parts.renderTail policy psTail (k (policy.step st tk) r) prest
        (gap.toChars ++ r ++ rest, st')
    | .hole e' _ :: psTail,  (gap, st, k),  .hole ex prest =>
        let (r, stAfter) := Expr.render policy st e' ex
        let (rest, st') := Parts.renderTail policy psTail (k stAfter r) prest
        (gap.toChars ++ r ++ rest, st')
end

/-- Top-level render for a loosest tree: render it under `policy.initial`, then emit
the global trailing run. This is the `Renderer` fed to the `Biparser`. -/
def renderExpr {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (policy : Policy G) : List Char :=
  let (chars, st) := Expr.render policy policy.initial e ex
  chars ++ (policy.trail st).map (·.val)

end LambdaLab.Parser.Mixfix
