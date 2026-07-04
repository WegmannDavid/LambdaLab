import LambdaLab.Parser2.Mixfix.Tree

/-!
# Rendering, split at the token boundary (state-threaded)

`renderSp` walks the tree producing a **spaced token list** — each token with the
separator run before it (tokens in order are `Expr.flatten`) — while threading a
user `State` left-to-right. A trivial flat join (`spacedToChars`) gives `List Char`.

The single threaded `State` serves both use cases:
* **depth-aware layout** — `enter`/`exit` bump a depth on the way in/out of a hole
  (they balance, so it behaves like an inherited attribute), and `lead`/`gap` read
  it to indent.
* **the `render_complete` cursor witness** — `State := List Char` (remaining input),
  `lead`/`gap` `readSeps` off it, `step` drops a rendered token; so rendering
  reproduces the input.
-/

namespace LambdaLab.Parser2.Mixfix

open LambdaLab.Parser2

/-- A rendering **policy**: a user `State` threaded left-to-right. `lead`/`gap`
produce a separator run *and* the state after emitting it; `step` advances past a
token; `enter`/`exit` bracket a hole (depth); `trail` is the final trailing run. -/
structure Policy (G : Grammar) where
  State   : Type
  initial : State
  lead    : State → List (Sep G) × State
  gap     : State → (e : G.Ent) → (o : (G.entry e).Op) → Nat → NESep G × State
  step    : State → Token G.isSep → State
  enter   : State → State
  exit    : State → State
  trail   : State → List (Sep G)

mutual
  /-- Render `ex` at `state`, with `lead` the run before its first token; returns the
  spaced token list and the final state. -/
  def Expr.renderSp {G : Grammar} (policy : Policy G) (state : policy.State)
      (lead : List (Sep G)) {e : G.Ent} {l : Level (G.entry e)} :
      Expr G e l → List (List (Sep G) × Token G.isSep) × policy.State
    | .var t _      => ([(lead, t)], policy.step state t)
    | .op o _ parts => Parts.renderSp policy state lead e o parts

  /-- The body's first part takes the incoming `lead`; the rest go through
  `renderSpTail`. -/
  def Parts.renderSp {G : Grammar} (policy : Policy G) (state : policy.State)
      (lead : List (Sep G)) (e : G.Ent) (o : (G.entry e).Op) :
      {ps : List (Part G)} → Parts G ps → List (List (Sep G) × Token G.isSep) × policy.State
    | _, .nil              => ([], state)
    | _, .namePart tk rest =>
        let (rp, s') := Parts.renderSpTail policy (policy.step state tk) e o 0 rest
        ((lead, tk) :: rp, s')
    | _, .hole ex rest     =>
        let (cp, s1) := Expr.renderSp policy (policy.enter state) lead ex
        let (rp, s2) := Parts.renderSpTail policy (policy.exit s1) e o 0 rest
        (cp ++ rp, s2)

  /-- The remaining parts: part `i` takes `gap … i` (which also advances the state). -/
  def Parts.renderSpTail {G : Grammar} (policy : Policy G) (state : policy.State)
      (e : G.Ent) (o : (G.entry e).Op) (i : Nat) :
      {ps : List (Part G)} → Parts G ps → List (List (Sep G) × Token G.isSep) × policy.State
    | _, .nil              => ([], state)
    | _, .namePart tk rest =>
        let (g, s0) := policy.gap state e o i
        let (rp, s') := Parts.renderSpTail policy (policy.step s0 tk) e o (i + 1) rest
        ((g.toList, tk) :: rp, s')
    | _, .hole ex rest     =>
        let (g, s0) := policy.gap state e o i
        let (cp, s1) := Expr.renderSp policy (policy.enter s0) g.toList ex
        let (rp, s2) := Parts.renderSpTail policy (policy.exit s1) e o (i + 1) rest
        (cp ++ rp, s2)
end

/-- The flat join: a spaced token list to chars. -/
def spacedToChars {G : Grammar} (parts : List (List (Sep G) × Token G.isSep)) : List Char :=
  parts.flatMap (fun p => p.1.map (·.val) ++ p.2.val.toList)

/-- Top-level render: emit the leading run, render the spaced token list, join, then
the trailing run. This is the `Renderer` fed to the `Biparser`. -/
def renderExpr {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (policy : Policy G) : List Char :=
  let (leadRun, s0) := policy.lead policy.initial
  let (parts, sFinal) := Expr.renderSp policy s0 leadRun ex
  spacedToChars parts ++ (policy.trail sFinal).map (·.val)

end LambdaLab.Parser2.Mixfix
