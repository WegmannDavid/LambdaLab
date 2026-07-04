import LambdaLab.Parser1.Mixfix.Render
import LambdaLab.Parser1.Mixfix.Parse
import LambdaLab.Parser1.Mixfix.Verified

/-!
# Assembling the mixfix `Biparser`

`biparser` bundles the char-level `parseChars` (tokenize + token parse) with the
policy-driven `renderExpr` into a `Biparser Char (Policy G) (Expr G e .loosest)`.
The two coherence laws (`render_complete`, `parse_complete`) are left as `sorry`
for now — the definitions come first.
-/

namespace LambdaLab.Parser1.Mixfix

open LambdaLab.Parser1

/-! ## The `render_complete` witness (cursor policy)

The witness `State` is the **remaining input**. `traverse`/`traverseVar` read the
actual separator runs off it and advance past each rendered part, so rendering `ex`
reproduces the input verbatim. -/

/-- The leading run of separator characters of a char list, carrying the `isSep`
proofs. -/
def readSeps {G : Grammar} : List Char → List (Sep G)
  | []        => []
  | c :: rest => if h : G.isSep c = true then ⟨c, h⟩ :: readSeps rest else []

/-- Promote a possibly-empty separator run to a `NESep`, falling back to `dflt` when
empty (only reached at a would-be gap that has no separator — never on valid input). -/
def mkNESep {G : Grammar} (dflt : Sep G) : List (Sep G) → NESep G
  | []        => ⟨dflt, []⟩
  | c :: rest => ⟨c, rest⟩

/-- Read the telescope tail off the remaining input: each gap is the actual
separator run there; each continuation drops the rendered part's chars. -/
def cursorTail {G : Grammar} (dflt : Sep G) :
    List Char → (ps : List (Part G)) → LayoutTail G (List Char) ps
  | remaining, []      => let ss := readSeps (G := G) remaining; (ss, remaining.drop ss.length)
  | remaining, _ :: ps =>
      let gap := readSeps remaining
      let remAfter := remaining.drop gap.length
      (mkNESep dflt gap, remAfter, fun r => cursorTail dflt (remAfter.drop r.length) ps)

/-- Like `cursorTail`, but the first separator run is the (possibly-empty) left
edge. -/
def cursorLayout {G : Grammar} (dflt : Sep G) :
    List Char → (ps : List (Part G)) → Layout G (List Char) ps
  | remaining, []      => let ss := readSeps (G := G) remaining; (ss, remaining.drop ss.length)
  | remaining, _ :: ps =>
      let edge := readSeps remaining
      let remAfter := remaining.drop edge.length
      (edge, remAfter, fun r => cursorTail dflt (remAfter.drop r.length) ps)

/-- The cursor witness policy: `State` is the remaining input. A variable's right
edge is nonempty only when the rest of the input is entirely separators (i.e. it is
the whole tree, so those are trailing whitespace); otherwise the parent's gaps
already surround it, so it is `[]`. -/
def cursorPolicy {G : Grammar} (dflt : Sep G) (input : List Char) : Policy G where
  State       := List Char
  initial     := input
  traverse    := fun e o remaining => cursorLayout dflt remaining (Operator.body e o)
  traverseVar := fun _ t remaining =>
    let leftEdge   := readSeps remaining
    let afterToken := (remaining.drop leftEdge.length).drop t.val.toList.length
    let afterSeps  := readSeps afterToken
    (leftEdge, if afterSeps.length = afterToken.length then afterSeps else [])

/-! ### `readSeps` characterisation

`readSeps` is exactly `takeWhile isSep`, so advancing past it is `dropWhile isSep` —
the primitive the cursor render uses at every separator boundary. -/

theorem readSeps_map {G : Grammar} (l : List Char) :
    (readSeps (G := G) l).map (·.val) = l.takeWhile G.isSep := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    unfold readSeps
    split
    · rename_i hc; simp [hc, ih]
    · rename_i hc; simp [hc]

theorem readSeps_length {G : Grammar} (l : List Char) :
    (readSeps (G := G) l).length = (l.takeWhile G.isSep).length := by
  rw [← readSeps_map, List.length_map]

theorem readSeps_drop {G : Grammar} (l : List Char) :
    l.drop (readSeps (G := G) l).length = l.dropWhile G.isSep := by
  rw [readSeps_length]
  induction l with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : G.isSep c = true <;>
      simp [hc, List.drop_succ_cons, ih]

/-- **Heart of `render_complete`**: the cursor witness reproduces the input. Reduces
to a tokenizer-inverse characterisation (`input` = tokens interleaved with the
separator runs `readSeps` recovers) plus an induction that `render` walks `ex` in
lockstep with that cursor, using `ex.flatten = tokenize G input` (`parse_sound`). -/
theorem cursor_render {G : Grammar} (dflt : Sep G) (input : List Char)
    {e : G.Ent} (ex : Expr G e .loosest) (h : ex ∈ parse e (tokenize G input)) :
    renderExpr ex (cursorPolicy dflt input) = input := by
  sorry

/-- The mixfix biparser at start entry `e`: parse chars into a loosest tree, render
a tree back to chars under a `Policy G`. -/
def biparser {G : Grammar} {e : G.Ent} : Biparser Char (Policy G) (Expr G e .loosest) where
  render          := renderExpr
  parse           := parseChars e
  render_complete := by
    intro input ex s hmem
    cases input with
    | nil => simp [parseChars] at hmem
    | cons c cs =>
      simp only [parseChars, List.mem_map] at hmem
      obtain ⟨ex', hex', heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ heq
      -- Goal: `∃ p, renderExpr ex p = c :: cs`, given `ex ∈ parse e (tokenize G (c::cs))`.
      -- The witness is `cursorPolicy dflt (c :: cs)` and the equation is `cursor_render`;
      -- what remains is (a) `cursor_render` itself and (b) producing the default separator
      -- `dflt : Sep G` (extractable from the input whenever it has an internal gap).
      sorry
  parse_complete := by
    intro ex p rest
    -- `parseChars` only returns *full* parses (`s.list = []`), so the required `s` with
    -- `s.list = rest` cannot exist when `rest ≠ []`. This law is UNPROVABLE until
    -- `parseChars` is rewritten as a prefix parser (leaving a char-level leftover).
    sorry

/-- The **token-level** mixfix biparser: `parse` is the precedence parser, `render`
is `flatten`, and there is nothing to choose (`Policy := Unit`). Both laws hold
outright — `render_complete` is `parseExpr_sound`, `parse_complete` is
`parseExpr_complete`. This is the verified core; a char-level biparser is this
composed with a tokenizer. -/
def tokenBiparser {G : Grammar} {e : G.Ent} : Biparser (Token G.isSep) Unit (Expr G e .loosest) where
  render          := fun ex _ => ex.flatten
  parse           := fun tkns => parseExpr e .loosest tkns
  render_complete := by
    intro input ex s hmem
    refine ⟨(), ?_⟩
    show ex.flatten = s.pre
    have hsound : ex.flatten ++ s.list = input := parseExpr_sound (x := (ex, s)) hmem
    have h : ex.flatten ++ s.list = s.pre ++ s.list := hsound.trans s.eq.symm
    have hlen : ex.flatten.length = s.pre.length := by
      have hl := congrArg List.length h
      simp [List.length_append] at hl
      omega
    exact (List.append_inj h hlen).1
  parse_complete := by
    intro ex _ rest
    exact parseExpr_complete ex (ex.flatten ++ rest) rest rfl

end LambdaLab.Parser1.Mixfix
