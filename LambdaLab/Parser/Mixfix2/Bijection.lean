import LambdaLab.Parser.Mixfix2.Tree

/-!
# Flatten / parse bijection (Mixfix2)

`flatten` turns a tree into its token stream; `parse` is intended to be
its inverse. The bijection is the pair of round-trips

* `parse (flatten t) = some t`
* `parse s = some t → flatten t = s`

This file provides `flatten`, `parse` (closed fragment), and the
soundness direction.
-/

namespace LambdaLab.Parser.Mixfix2

/-! ## Weaving name-parts and child token-lists -/

/-- `closed`: `n₀ c₀ n₁ c₁ … nₖ` — name-parts on the outside. -/
def weaveClosed : List String → List (List String) → List String
  | [],          _       => []
  | [p],         _       => [p]
  | p :: _ :: _, []      => [p]
  | p :: ps,     c :: cs => p :: c ++ weaveClosed ps cs

/-- `prefix`: `n₀ c₀ n₁ c₁ … nₖ cₖ` — a child after every name-part. -/
def weavePrefix : List String → List (List String) → List String
  | [],      _       => []
  | _ :: _,  []      => []
  | p :: ps, c :: cs => p :: c ++ weavePrefix ps cs

/-- `postfix`: `c₀ n₀ c₁ n₁ … cₖ nₖ` — a child before every name-part. -/
def weavePostfix : List String → List (List String) → List String
  | [],      _       => []
  | _ :: _,  []      => []
  | p :: ps, c :: cs => c ++ p :: weavePostfix ps cs

/-- `infix`: `c₀ n₀ c₁ n₁ … nₖ cₖ₊₁` — children on the outside. -/
def weaveInfix : List String → List (List String) → List String
  | [],      []       => []
  | [],      [c]      => c
  | [],      _ :: _   => []
  | _ :: _,  []       => []
  | p :: ps, c :: cs  => c ++ p :: weaveInfix ps cs

/-! ## Flatten -/

mutual
  /-- Token stream of a tree. `top` flattens its node; `next` is a pure
  weakening and flattens its subtree unchanged. -/
  def Tree.flatten {G d} : Tree G d → List String
    | .top n  => n.flatten
    | .next t => t.flatten

  /-- Token stream of a node: weave the operator's name-parts with the
  flattened children, dispatched on fixity. -/
  def Node.flatten {G d} : Node G d → List String
    | .mk h cs =>
        let parts := cs.flatten
        let Op := G.ops[d]'h
        match Op.fixity with
        | .closed  => weaveClosed  Op.nameParts parts
        | .prefix  => weavePrefix  Op.nameParts parts
        | .postfix => weavePostfix Op.nameParts parts
        | .infix _ => weaveInfix   Op.nameParts parts

  /-- Flattened children, in token order. -/
  def Children.flatten {G Ls} : Children G Ls → List (List String)
    | .nil       => []
    | .cons t cs => t.flatten :: cs.flatten
end

/-! ## Parsing (closed fragment)

`parse` is recursive-descent over precedence levels (depths into `G`).
It is restricted, for now, to operators that begin with a name-part —
`closed` operators (and the nullary `closed` constants); other fixities
are skipped via `next`.

Termination is well-founded on `(s.length, G.length - d)` lexicographically.
`parse` returns a *sized* suffix `Rest s` (`{ r // r.length ≤ s.length }`)
so each recursive call carries the bound the measure needs. -/

/-- Build the homogeneous interior children of a closed operator (all at
the loosest level `0`) from a plain list of trees. -/
def listToChildren {G : Grammar} :
    (cs : List (Tree G 0)) → Children G (List.replicate cs.length 0)
  | []      => .nil
  | c :: cs => .cons c (listToChildren cs)

theorem childLevels_closed (Op : Operator) (d : Nat) (h : Op.fixity = .closed) :
    Op.childLevels d = List.replicate (Op.nameParts.length - 1) 0 := by
  simp [Operator.childLevels, h]

@[simp] theorem listToChildren_flatten {G : Grammar} (cs : List (Tree G 0)) :
    (listToChildren cs).flatten = cs.map (·.flatten) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [listToChildren, Children.flatten, ih]

theorem Children.flatten_cast {G : Grammar} {Ls₁ Ls₂ : List Nat}
    (h : Ls₁ = Ls₂) (x : Children G Ls₁) : (h ▸ x).flatten = x.flatten := by
  cases h; rfl

/-- The index equality witnessing that a length-matched list of trees has
exactly a closed operator's child-levels. -/
theorem childLevels_closed_replicate (Op : Operator) (d : Nat)
    (h : Op.fixity = .closed) (cs : List (Tree G 0))
    (hlen : cs.length = Op.nameParts.length - 1) :
    Op.childLevels d = List.replicate cs.length 0 := by
  rw [childLevels_closed Op d h, hlen]

/-- Smart constructor for a closed node from its interior children given
as a length-matched list. The operator at depth `d` is `G.ops[d]`. -/
def Node.mkClosed {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hc : (G.ops[d]'h).fixity = .closed) (cs : List (Tree G 0))
    (hlen : cs.length = (G.ops[d]'h).nameParts.length - 1) : Node G d :=
  .mk h ((childLevels_closed_replicate (G.ops[d]'h) d hc cs hlen).symm ▸ listToChildren cs)

/-! ### Heterogeneous-children smart constructors for the non-closed fixities

Unlike `closed` (all interior children at level `0`), the prefix/postfix/
infix operators have a leading and/or trailing hole at a different level.
We build their `Children` lists from a homogeneous interior plus the
extra hole(s), then cast along the corresponding `childLevels` equality. -/

/-- Append a trailing tree to a children list. -/
def Children.snoc {G : Grammar} {Ls : List Nat} {L : Nat} :
    Children G Ls → Tree G L → Children G (Ls ++ [L])
  | .nil,       t => .cons t .nil
  | .cons c cs, t => .cons c (cs.snoc t)

@[simp] theorem Children.snoc_flatten {G : Grammar} {Ls : List Nat} {L : Nat}
    (cs : Children G Ls) (t : Tree G L) :
    (cs.snoc t).flatten = cs.flatten ++ [t.flatten] := by
  match cs with
  | .nil => rfl
  | .cons c cs => simp [Children.snoc, Children.flatten, Children.snoc_flatten cs t]

/-- `prefix` children: interior (level 0) then the trailing hole (level `d`). -/
def childrenPrefix {G : Grammar} {d : Nat}
    (interior : List (Tree G 0)) (trailing : Tree G d) :
    Children G (List.replicate interior.length 0 ++ [d]) :=
  (listToChildren interior).snoc trailing

/-- `postfix` children: the leading hole (level `d`) then interior (level 0). -/
def childrenPostfix {G : Grammar} {d : Nat}
    (leading : Tree G d) (interior : List (Tree G 0)) :
    Children G (d :: List.replicate interior.length 0) :=
  .cons leading (listToChildren interior)

/-- `infix` children: leading (level `L`), interior (level 0), trailing (level `R`). -/
def childrenInfix {G : Grammar} {L R : Nat}
    (leading : Tree G L) (interior : List (Tree G 0)) (trailing : Tree G R) :
    Children G (L :: (List.replicate interior.length 0 ++ [R])) :=
  .cons leading ((listToChildren interior).snoc trailing)

theorem childLevels_prefix (Op : Operator) (d : Nat) (h : Op.fixity = .prefix) :
    Op.childLevels d = List.replicate (Op.nameParts.length - 1) 0 ++ [d] := by
  simp [Operator.childLevels, h]

theorem childLevels_postfix (Op : Operator) (d : Nat) (h : Op.fixity = .postfix) :
    Op.childLevels d = d :: List.replicate (Op.nameParts.length - 1) 0 := by
  simp [Operator.childLevels, h]

theorem childLevels_infix_left (Op : Operator) (d : Nat) (h : Op.fixity = .infix .left) :
    Op.childLevels d = d :: (List.replicate (Op.nameParts.length - 1) 0 ++ [d + 1]) := by
  simp [Operator.childLevels, h]

theorem childLevels_prefix' {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .prefix) (interior : List (Tree G 0))
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) :
    (G.ops[d]'h).childLevels d = List.replicate interior.length 0 ++ [d] := by
  rw [childLevels_prefix _ d hf, hlen]

def Node.mkPrefix {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .prefix)
    (interior : List (Tree G 0)) (trailing : Tree G d)
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) : Node G d :=
  .mk h ((childLevels_prefix' h hf interior hlen).symm ▸ childrenPrefix interior trailing)

theorem Node.mkPrefix_flatten {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .prefix)
    (interior : List (Tree G 0)) (trailing : Tree G d)
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) :
    (Node.mkPrefix h hf interior trailing hlen).flatten
      = weavePrefix (G.ops[d]'h).nameParts (interior.map (·.flatten) ++ [trailing.flatten]) := by
  unfold Node.mkPrefix Node.flatten
  simp only [hf]
  rw [Children.flatten_cast]
  simp [childrenPrefix, listToChildren_flatten]

theorem childLevels_postfix' {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .postfix) (interior : List (Tree G 0))
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) :
    (G.ops[d]'h).childLevels d = d :: List.replicate interior.length 0 := by
  rw [childLevels_postfix _ d hf, hlen]

def Node.mkPostfix {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .postfix)
    (leading : Tree G d) (interior : List (Tree G 0))
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) : Node G d :=
  .mk h ((childLevels_postfix' h hf interior hlen).symm ▸ childrenPostfix leading interior)

theorem Node.mkPostfix_flatten {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .postfix)
    (leading : Tree G d) (interior : List (Tree G 0))
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) :
    (Node.mkPostfix h hf leading interior hlen).flatten
      = weavePostfix (G.ops[d]'h).nameParts (leading.flatten :: interior.map (·.flatten)) := by
  unfold Node.mkPostfix Node.flatten
  simp only [hf]
  rw [Children.flatten_cast]
  simp [childrenPostfix, Children.flatten, listToChildren_flatten]

/-- Infix smart constructor. `L`/`R` (the leading/trailing hole levels)
depend on the associativity, so we take the `childLevels` equality as a
hypothesis; `ha : fixity = .infix a` is what reduces the flatten match. -/
def Node.mkInfix {G : Grammar} {d : Nat} {L R : Nat} (h : d < G.ops.size) (a : Associativity)
    (ha : (G.ops[d]'h).fixity = .infix a)
    (leading : Tree G L) (interior : List (Tree G 0)) (trailing : Tree G R)
    (hlevels : (G.ops[d]'h).childLevels d = L :: (List.replicate interior.length 0 ++ [R])) :
    Node G d :=
  .mk h (hlevels.symm ▸ childrenInfix leading interior trailing)

theorem Node.mkInfix_flatten {G : Grammar} {d : Nat} {L R : Nat} (h : d < G.ops.size)
    (a : Associativity) (ha : (G.ops[d]'h).fixity = .infix a)
    (leading : Tree G L) (interior : List (Tree G 0)) (trailing : Tree G R)
    (hlevels : (G.ops[d]'h).childLevels d = L :: (List.replicate interior.length 0 ++ [R])) :
    (Node.mkInfix h a ha leading interior trailing hlevels).flatten
      = weaveInfix (G.ops[d]'h).nameParts
          (leading.flatten :: (interior.map (·.flatten) ++ [trailing.flatten])) := by
  unfold Node.mkInfix Node.flatten
  simp only [ha]
  rw [Children.flatten_cast]
  simp [childrenInfix, Children.flatten, listToChildren_flatten]

/-- The unconsumed suffix returned by a parser: a token list provably no
longer than the input. -/
abbrev Rest (s : List String) : Type := { r : List String // r.length ≤ s.length }

/-- Discharge a `Prod.Lex` (triple) termination goal of the shape produced
by `parse`'s measure: first try a strict decrease of the length component,
then (length equal) the level component, then the phase component. -/
theorem lex_triple_lt {a₁ a₂ b₁ b₂ c₁ c₂ : Nat}
    (h : a₁ < a₂ ∨ (a₁ = a₂ ∧ (b₁ < b₂ ∨ (b₁ = b₂ ∧ c₁ < c₂)))) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a₁, b₁, c₁) (a₂, b₂, c₂) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · refine Prod.Lex.right _ ?_
    rcases h with h | ⟨rfl, h⟩
    · exact Prod.Lex.left _ _ h
    · exact Prod.Lex.right _ h

/-- Termination tactic for the `parse` mutual block. -/
syntax "lex_tac" : tactic
macro_rules
  | `(tactic| lex_tac) => `(tactic| simp_wf <;> (apply lex_triple_lt <;> omega))

section
variable (G : Grammar)

mutual
  /-- Parse a tree at level `d` from `s`, returning it with the unconsumed
  suffix. The four fixities:

  * `closed`/`prefix` start with a name-part — try the matching body
    parser, else fall through (`next`) to the tighter level `d + 1`.
  * `postfix`/`infix` start with a hole at level `d` (left recursion).
    We avoid the recursion by precedence-climbing: parse a *tighter*
    leading operand (level `d + 1`), then `parseTail` iterates, folding
    in any further occurrences of the operator at level `d`.

  Termination is well-founded on `(s.length, G.ops.size - d, phase)`
  lexicographically: `parse` has phase `2`, `parseTail` phase `1`, the
  body parsers phase `0`. A `next` step keeps the length but lowers the
  level; the `parse → parseTail` step keeps both but lowers the phase;
  every `parseTail` iteration strictly shortens the input. -/
  def parse : (d : Nat) → (s : List String) → Option (Tree G d × Rest s)
    | d, s =>
        if h : d < G.ops.size then
          match hf : (G.ops[d]'h).fixity with
          | .closed =>
              match parseClosedBody (G.ops[d]'h).nameParts s with
              | some (cs, r) =>
                  if hlen : cs.length = (G.ops[d]'h).nameParts.length - 1 then
                    some (.top (Node.mkClosed h hf cs hlen), r)
                  else
                    match parse (d + 1) s with
                    | some (t, r) => some (.next t, r)
                    | none        => none
              | none =>
                  match parse (d + 1) s with
                  | some (t, r) => some (.next t, r)
                  | none        => none
          | .prefix =>
              match parsePrefixBody d (G.ops[d]'h).nameParts s with
              | some (interior, trailing, ⟨r, hr⟩) =>
                  if hlen : interior.length = (G.ops[d]'h).nameParts.length - 1 then
                    some (.top (Node.mkPrefix h hf interior trailing hlen), ⟨r, by omega⟩)
                  else
                    match parse (d + 1) s with
                    | some (t, r) => some (.next t, r)
                    | none        => none
              | none =>
                  match parse (d + 1) s with
                  | some (t, r) => some (.next t, r)
                  | none        => none
          | .postfix =>
              match parse (d + 1) s with
              | some (t, ⟨r, hr⟩) =>
                  match parseTail d (.next t) r with
                  | (t', ⟨res, hres⟩) => some (t', ⟨res, by omega⟩)
              | none => none
          | .infix _ =>
              match parse (d + 1) s with
              | some (t, ⟨r, hr⟩) =>
                  match parseTail d (.next t) r with
                  | (t', ⟨res, hres⟩) => some (t', ⟨res, by omega⟩)
              | none => none
        else none
  termination_by d s => (s.length, G.ops.size - d, 2)
  decreasing_by
    all_goals lex_tac

  /-- The left-fold loop. Given an already-parsed `acc : Tree G d`, extend
  it by repeatedly consuming the operator at level `d` whenever its leading
  name-part appears next:

  * `postfix` — wrap `acc` as the leading hole, fold, loop;
  * `infix .left` — parse a tighter right operand (the body parser puts the
    trailing hole at `d + 1`), fold left, loop.

  For the other fixities (and out of bounds) it is the identity: those are
  handled by `parse` directly, not by the loop. Each iteration consumes at
  least the operator's leading name-part, so the input strictly shrinks. -/
  def parseTail (d : Nat) (acc : Tree G d) (r : List String) :
      Tree G d × Rest r :=
    if h : d < G.ops.size then
      match hf : (G.ops[d]'h).fixity with
      | .postfix =>
          match parsePostfixBody (G.ops[d]'h).nameParts r with
          | some (interior, ⟨r', hr'⟩) =>
              if hlen : interior.length = (G.ops[d]'h).nameParts.length - 1 then
                match parseTail d (.top (Node.mkPostfix h hf acc interior hlen)) r' with
                | (t', ⟨res, hres⟩) => (t', ⟨res, by omega⟩)
              else (acc, ⟨r, Nat.le_refl _⟩)
          | none => (acc, ⟨r, Nat.le_refl _⟩)
      | .infix .left =>
          match parsePrefixBody (d + 1) (G.ops[d]'h).nameParts r with
          | some (interior, trailing, ⟨r', hr'⟩) =>
              if hlen : interior.length = (G.ops[d]'h).nameParts.length - 1 then
                match parseTail d
                    (.top (Node.mkInfix h .left hf acc interior trailing
                      (by rw [childLevels_infix_left _ d hf, hlen]))) r' with
                | (t', ⟨res, hres⟩) => (t', ⟨res, by omega⟩)
              else (acc, ⟨r, Nat.le_refl _⟩)
          | none => (acc, ⟨r, Nat.le_refl _⟩)
      | _ => (acc, ⟨r, Nat.le_refl _⟩)
    else (acc, ⟨r, Nat.le_refl _⟩)
  termination_by (r.length, G.ops.size - d, 1)
  decreasing_by
    all_goals lex_tac

  /-- Parse the body of a closed operator: name-parts on the outside,
  interior children (each at level `0`) in between. -/
  def parseClosedBody : (names : List String) → (s : List String) →
      Option (List (Tree G 0) × Rest s)
    | [],            _ => none
    | [_n],          s =>
        match s with
        | t :: r => if t = _n then some ([], ⟨r, by simp⟩) else none
        | []     => none
    | n :: n' :: ns, s =>
        match s with
        | t :: r₀ =>
            if t = n then
              match parse 0 r₀ with
              | some (c, ⟨r₁, h₁⟩) =>
                  match parseClosedBody (n' :: ns) r₁ with
                  | some (cs, ⟨r₂, h₂⟩) =>
                      some (c :: cs, ⟨r₂, by simp only [List.length_cons]; omega⟩)
                  | none => none
              | none => none
            else none
        | [] => none
  termination_by _names s => (s.length, 0, 0)
  decreasing_by
    all_goals lex_tac

  /-- Prefix body: a child after every name-part; all but the last at level
  `0`, the last (trailing) at level `d`. The returned rest is *strictly*
  shorter (the leading name-part is always consumed) — `parse`'s `prefix`
  branch weakens that to `≤`, while the `infix .left` `parseTail` loop uses
  the strict bound to terminate (reusing this parser with `d := d + 1`, so
  the trailing operand lands at the tighter level). -/
  def parsePrefixBody (d : Nat) : (names : List String) → (s : List String) →
      Option (List (Tree G 0) × Tree G d × { r : List String // r.length < s.length })
    | [],            _ => none
    | [_n],          s =>
        match s with
        | t :: r₀ =>
            if t = _n then
              match parse d r₀ with
              | some (c, ⟨r₁, h₁⟩) => some ([], c, ⟨r₁, by simp; omega⟩)
              | none => none
            else none
        | [] => none
    | n :: n' :: ns, s =>
        match s with
        | t :: r₀ =>
            if t = n then
              match parse 0 r₀ with
              | some (c, ⟨r₁, h₁⟩) =>
                  match parsePrefixBody d (n' :: ns) r₁ with
                  | some (cs, trailing, ⟨r₂, h₂⟩) =>
                      some (c :: cs, trailing, ⟨r₂, by simp; omega⟩)
                  | none => none
              | none => none
            else none
        | [] => none
  termination_by _names s => (s.length, 0, 0)
  decreasing_by
    all_goals lex_tac

  /-- Postfix body *after* the leading operand: `n₀ c₁ n₁ … cₖ nₖ` — a
  name-part, then (child·name)* . All interior children at level `0`; there
  is no trailing child. The returned rest is *strictly* shorter, which is
  what lets the `parseTail` postfix loop terminate. -/
  def parsePostfixBody : (names : List String) → (s : List String) →
      Option (List (Tree G 0) × { r : List String // r.length < s.length })
    | [],            _ => none
    | [_n],          s =>
        match s with
        | t :: r => if t = _n then some ([], ⟨r, by simp⟩) else none
        | []     => none
    | n :: n' :: ns, s =>
        match s with
        | t :: r₀ =>
            if t = n then
              match parse 0 r₀ with
              | some (c, ⟨r₁, h₁⟩) =>
                  match parsePostfixBody (n' :: ns) r₁ with
                  | some (cs, ⟨r₂, h₂⟩) =>
                      some (c :: cs, ⟨r₂, by simp only [List.length_cons]; omega⟩)
                  | none => none
              | none => none
            else none
        | [] => none
  termination_by _names s => (s.length, 0, 0)
  decreasing_by
    all_goals lex_tac
end

end

/-! ## Soundness: whatever `parse` returns flattens back

`parse d s = some (t, r)` implies `t.flatten ++ r.val = s`. No grammar
hypotheses are needed — this direction is pure bookkeeping. -/

theorem Node.mkClosed_flatten {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hc : (G.ops[d]'h).fixity = .closed) (cs : List (Tree G 0))
    (hlen : cs.length = (G.ops[d]'h).nameParts.length - 1) :
    (Node.mkClosed h hc cs hlen).flatten
      = weaveClosed (G.ops[d]'h).nameParts (cs.map (·.flatten)) := by
  unfold Node.mkClosed Node.flatten
  simp only [hc]
  rw [Children.flatten_cast, listToChildren_flatten]

theorem Node.mkPrefix_flatten' {G : Grammar} {d : Nat} (h : d < G.ops.size)
    (hf : (G.ops[d]'h).fixity = .prefix)
    (interior : List (Tree G 0)) (trailing : Tree G d)
    (hlen : interior.length = (G.ops[d]'h).nameParts.length - 1) :
    (Tree.top (Node.mkPrefix h hf interior trailing hlen)).flatten
      = weavePrefix (G.ops[d]'h).nameParts (interior.map (·.flatten) ++ [trailing.flatten]) := by
  simp [Tree.flatten, Node.mkPrefix_flatten]

/-- The leading hole of an `infix` peels off a `weavePrefix` over the rest:
the leading operand prints first, then `weaveInfix` over the remaining
holes coincides with `weavePrefix`. Used to bridge `parseTail`'s left-fold
(which reuses `parsePrefixBody` for the right operand) and `weaveInfix`. -/
theorem weaveInfix_cons (names : List String) (cs : List (List String))
    (hlen : names.length = cs.length) :
    ∀ lead, weaveInfix names (lead :: cs) = lead ++ weavePrefix names cs := by
  induction names generalizing cs with
  | nil =>
      intro lead
      cases cs with
      | nil => simp [weaveInfix, weavePrefix]
      | cons c cs => simp at hlen
  | cons n ns ih =>
      intro lead
      cases cs with
      | nil => simp at hlen
      | cons c cs => simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
                     simp [weaveInfix, weavePrefix, ih cs hlen]

/-- Parse soundness, as a motive over `parse`. -/
def Sound1 (G : Grammar) (d : Nat) (s : List String) : Prop :=
  ∀ (t : Tree G d) (r : Rest s), parse G d s = some (t, r) → t.flatten ++ r.val = s

/-- `parseTail` soundness: the loop extends `acc` by consuming a prefix of
`r`, so the result's flatten plus its leftover equals `acc.flatten ++ r`. -/
def SoundTail (G : Grammar) (d : Nat) (acc : Tree G d) (r : List String) : Prop :=
  ∀ (t' : Tree G d) (res : Rest r), parseTail G d acc r = (t', res) →
    t'.flatten ++ res.val = acc.flatten ++ r

/-- Closed-body soundness, as a motive over `parseClosedBody`. -/
def Sound2 (G : Grammar) (names s : List String) : Prop :=
  ∀ (cs : List (Tree G 0)) (r : Rest s), parseClosedBody G names s = some (cs, r) →
    weaveClosed names (cs.map (·.flatten)) ++ r.val = s ∧ cs.length = names.length - 1

/-- Prefix-body soundness: name-parts and interior children printed in order,
trailing child at the end, all preceding the leftover `r`. -/
def SoundPrefix (G : Grammar) (d : Nat) (names s : List String) : Prop :=
  ∀ (interior : List (Tree G 0)) (trailing : Tree G d)
    (r : { r : List String // r.length < s.length }),
    parsePrefixBody G d names s = some (interior, trailing, r) →
      weavePrefix names (interior.map (·.flatten) ++ [trailing.flatten]) ++ r.val = s
        ∧ interior.length = names.length - 1

/-- Postfix-body soundness: the consumed tokens form the postfix tail after
*any* leading operand, independent of that operand. -/
def SoundPostfix (G : Grammar) (names s : List String) : Prop :=
  ∀ (interior : List (Tree G 0)) (r : { r : List String // r.length < s.length }),
    parsePostfixBody G names s = some (interior, r) →
      (∀ lead, weavePostfix names (lead :: interior.map (·.flatten)) ++ r.val = lead ++ s)
        ∧ interior.length = names.length - 1

/-- The `next` (level-descent) tail: when `parse (d+1) s = some (t,r)`, the
wrapped `Tree.next t` flattens identically. Shared by every fall-through
arm of `parse` (closed/prefix body-miss or length-mismatch). -/
theorem next_sound {G : Grammar} (d : Nat) (s : List String) (t : Tree G (d + 1))
    (r : Rest s) (t' : Tree G d) (r' : Rest s)
    (hpar : parse G (d + 1) s = some (t, r))
    (heq : (match parse G (d + 1) s with
        | some (t, r) => some (Tree.next t, r) | none => none) = some (t', r'))
    (ih : Sound1 G (d + 1) s) : t'.flatten ++ r'.val = s := by
  rw [hpar] at heq
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  simpa [Tree.flatten] using ih t r hpar

/- All five soundness motives, proved simultaneously by the
functional-induction principle of the `parse` mutual block (one principle,
five motives, 56 cases). The headline corollaries follow by projection. -/
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
theorem parse_sound_all (G : Grammar) : (∀ d s, Sound1 G d s) := by
  apply parse.induct G (Sound1 G) (SoundTail G) (SoundPrefix G) (SoundPostfix G) (Sound2 G)
  -- == Sound1 (parse), cases 1–15 ==========================================
  -- case1: closed, body some, length ok → `top`
  case case1 =>
    intro d s h hfc cs r hb hlen ih2 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfc] at hc; exact Fixity.noConfusion hc)
      | (simp only [hb, dif_pos hlen, Option.some.injEq, Prod.mk.injEq] at heq
         obtain ⟨rfl, rfl⟩ := heq
         obtain ⟨hbody, _⟩ := ih2 cs r hb
         simpa [Tree.flatten, Node.mkClosed_flatten] using hbody)
  -- case2: closed, body some, length wrong, parse(d+1) some → next
  case case2 =>
    intro d s h hfc cs r hb hnlen t₀ r₀ hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfc] at hc; exact Fixity.noConfusion hc)
      | (simp only [hb, dif_neg hnlen] at heq; exact next_sound _ _ _ _ _ _ hpar heq ih1)
  -- case3: closed, body some, length wrong, parse(d+1) none → fails
  case case3 =>
    intro d s h hfc cs r hb hnlen hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfc] at hc; exact Fixity.noConfusion hc)
      | (simp [hb, dif_neg hnlen, hpar] at heq)
  -- case4: closed, body none, parse(d+1) some → next
  case case4 =>
    intro d s h hfc hb t₀ r₀ hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfc] at hc; exact Fixity.noConfusion hc)
      | (simp only [hb] at heq; exact next_sound _ _ _ _ _ _ hpar heq ih1)
  -- case5: closed, body none, parse(d+1) none → fails
  case case5 =>
    intro d s h hfc hb hpar ih2 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfc] at hc; exact Fixity.noConfusion hc)
      | (simp [hb, hpar] at heq)
  -- case6: prefix, body some, length ok → `top`
  case case6 =>
    intro d s h hfp interior trailing r hr hb hlen ih3 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfp] at hc; exact Fixity.noConfusion hc)
      | (simp only [hb, dif_pos hlen, Option.some.injEq, Prod.mk.injEq] at heq
         obtain ⟨rfl, hrr⟩ := heq
         obtain ⟨hbody, _⟩ := ih3 interior trailing ⟨r, hr⟩ hb
         subst hrr
         simpa [Node.mkPrefix_flatten'] using hbody)
  -- case7: prefix, body some, length wrong, parse(d+1) some → next
  case case7 =>
    intro d s h hfp interior trailing r hr hb hnlen t₀ r₀ hpar ih3 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfp] at hc; exact Fixity.noConfusion hc)
      | (simp only [hb, dif_neg hnlen] at heq; exact next_sound _ _ _ _ _ _ hpar heq ih1)
  -- case8: prefix, body some, length wrong, parse(d+1) none → fails
  case case8 =>
    intro d s h hfp interior trailing r hr hb hnlen hpar ih3 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfp] at hc; exact Fixity.noConfusion hc)
      | (simp [hb, dif_neg hnlen, hpar] at heq)
  -- case9: prefix, body none, parse(d+1) some → next
  case case9 =>
    intro d s h hfp hb t₀ r₀ hpar ih3 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfp] at hc; exact Fixity.noConfusion hc)
      | (simp only [hb] at heq; exact next_sound _ _ _ _ _ _ hpar heq ih1)
  -- case10: prefix, body none, parse(d+1) none → fails
  case case10 =>
    intro d s h hfp hb hpar ih3 ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfp] at hc; exact Fixity.noConfusion hc)
      | (simp [hb, hpar] at heq)
  -- case11: postfix, parse(d+1) some → parseTail
  case case11 =>
    intro d s h hfx t r hr hpar t₀ res hres htail ih1 ihtail t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (simp only [hpar, htail, Option.some.injEq, Prod.mk.injEq] at heq
         obtain ⟨rfl, rfl⟩ := heq
         have htail' := ihtail t₀ ⟨res, hres⟩ htail
         have hpar' := ih1 t ⟨r, hr⟩ hpar
         calc t₀.flatten ++ res = (Tree.next t).flatten ++ r := htail'
           _ = t.flatten ++ r := by simp [Tree.flatten]
           _ = s := hpar')
  -- case12: postfix, parse(d+1) none → fails
  case case12 =>
    intro d s h hfx hpar ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (simp [hpar] at heq)
  -- case13: infix, parse(d+1) some → parseTail
  case case13 =>
    intro d s h a hfx t r hr hpar t₀ res hres htail ih1 ihtail t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (simp only [hpar, htail, Option.some.injEq, Prod.mk.injEq] at heq
         obtain ⟨rfl, rfl⟩ := heq
         have htail' := ihtail t₀ ⟨res, hres⟩ htail
         have hpar' := ih1 t ⟨r, hr⟩ hpar
         calc t₀.flatten ++ res = (Tree.next t).flatten ++ r := htail'
           _ = t.flatten ++ r := by simp [Tree.flatten]
           _ = s := hpar')
  -- case14: infix, parse(d+1) none → fails
  case case14 =>
    intro d s h a hfx hpar ih1 t' r' heq
    unfold parse at heq; rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (simp [hpar] at heq)
  -- case15: out of bounds → `parse` is `none`
  case case15 =>
    intro d s hoob t' r' heq
    unfold parse at heq; rw [dif_neg hoob] at heq; simp at heq
  -- == SoundTail (parseTail), cases 16–23 ==================================
  -- case16: postfix, body some, length ok → fold then loop
  case case16 =>
    intro d acc r h hfx interior r' hr' hb hlen tRec resRec hresRec hrecEq ihPost ihTail
    intro t' res heq
    rw [parseTail] at heq
    rw [dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (exact absurd hfx (by assumption))
      | skip
    rw [hb] at heq
    dsimp only at heq
    rw [dif_pos hlen, hrecEq] at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hres2⟩ := heq
    have htail := ihTail tRec ⟨resRec, hresRec⟩ hrecEq
    obtain ⟨hpost, _⟩ := ihPost interior ⟨r', hr'⟩ hb
    have hacc' :
        (Tree.top (Node.mkPostfix h hfx acc interior hlen)).flatten
          = weavePostfix (G.ops[d]'h).nameParts (acc.flatten :: interior.map (·.flatten)) := by
      simp [Tree.flatten, Node.mkPostfix_flatten]
    have hrv : res.val = resRec := by rw [← hres2]
    rw [hrv]
    calc tRec.flatten ++ resRec
          = (Tree.top (Node.mkPostfix h hfx acc interior hlen)).flatten ++ r' := htail
        _ = weavePostfix (G.ops[d]'h).nameParts (acc.flatten :: interior.map (·.flatten)) ++ r' := by
              rw [hacc']
        _ = acc.flatten ++ r := hpost acc.flatten
  -- case17: postfix, body some, length wrong → identity
  case case17 =>
    intro d acc r h hfx interior r' hr' hb hnlen ihPost t' res heq
    rw [parseTail, dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (exact absurd hfx (by assumption))
      | skip
    rw [hb] at heq; dsimp only at heq; rw [dif_neg hnlen] at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hr2⟩ := heq
    have hrv : res.val = r := by rw [← hr2]
    rw [hrv]
  -- case18: postfix, body none → identity
  case case18 =>
    intro d acc r h hfx hb ihPost t' res heq
    rw [parseTail, dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (exact absurd hfx (by assumption))
      | skip
    rw [hb] at heq; dsimp only at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hr2⟩ := heq
    have hrv : res.val = r := by rw [← hr2]
    rw [hrv]
  -- case19: infix .left, body some, length ok → fold then loop
  case case19 =>
    intro d acc r h hfx interior trailing r' hr' hb hlen tRec resRec hresRec hrecEq ihPref ihTail
    intro t' res heq
    rw [parseTail, dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (exact absurd hfx (by assumption))
      | skip
    rw [hb] at heq; dsimp only at heq; rw [dif_pos hlen, hrecEq] at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hres2⟩ := heq
    have htail := ihTail tRec ⟨resRec, hresRec⟩ hrecEq
    obtain ⟨hpref, hlen'⟩ := ihPref interior trailing ⟨r', hr'⟩ hb
    have hacc' :
        (Tree.top (Node.mkInfix h .left hfx acc interior trailing
            (by rw [childLevels_infix_left _ d hfx, hlen]))).flatten
          = weaveInfix (G.ops[d]'h).nameParts
              (acc.flatten :: (interior.map (·.flatten) ++ [trailing.flatten])) := by
      simp [Tree.flatten, Node.mkInfix_flatten]
    have hne : (G.ops[d]'h).nameParts ≠ [] := (G.ops[d]'h).nameParts_ne_nil
    have hpos : 0 < (G.ops[d]'h).nameParts.length := by
      cases hh : (G.ops[d]'h).nameParts with
      | nil => exact absurd hh hne
      | cons _ _ => simp [hh]
    have hlenmatch : (G.ops[d]'h).nameParts.length
        = (interior.map (·.flatten) ++ [trailing.flatten]).length := by
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega
    have hrv : res.val = resRec := by rw [← hres2]
    rw [hrv]
    calc tRec.flatten ++ resRec
          = (Tree.top (Node.mkInfix h .left hfx acc interior trailing
              (by rw [childLevels_infix_left _ d hfx, hlen]))).flatten ++ r' := htail
        _ = weaveInfix (G.ops[d]'h).nameParts
              (acc.flatten :: (interior.map (·.flatten) ++ [trailing.flatten])) ++ r' := by rw [hacc']
        _ = acc.flatten ++ weavePrefix (G.ops[d]'h).nameParts
              (interior.map (·.flatten) ++ [trailing.flatten]) ++ r' := by
              rw [weaveInfix_cons _ _ hlenmatch]
        _ = acc.flatten ++ (weavePrefix (G.ops[d]'h).nameParts
              (interior.map (·.flatten) ++ [trailing.flatten]) ++ r') := by
              rw [List.append_assoc]
        _ = acc.flatten ++ r := by rw [hpref]
  -- case20: infix .left, body some, length wrong → identity
  case case20 =>
    intro d acc r h hfx interior trailing r' hr' hb hnlen ihPref t' res heq
    rw [parseTail, dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (exact absurd hfx (by assumption))
      | skip
    rw [hb] at heq; dsimp only at heq; rw [dif_neg hnlen] at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hr2⟩ := heq
    have hrv : res.val = r := by rw [← hr2]
    rw [hrv]
  -- case21: infix .left, body none → identity
  case case21 =>
    intro d acc r h hfx hb ihPref t' res heq
    rw [parseTail, dif_pos h] at heq
    split at heq <;>
      first
      | (rename_i hc; rw [hfx] at hc; exact Fixity.noConfusion hc)
      | (exact absurd hfx (by assumption))
      | skip
    rw [hb] at heq; dsimp only at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hr2⟩ := heq
    have hrv : res.val = r := by rw [← hr2]
    rw [hrv]
  -- case22: any other fixity (closed/prefix/infix non-left) → identity
  case case22 =>
    intro d acc r h hnpost hninfl t' res heq
    rw [parseTail, dif_pos h] at heq
    split at heq <;>
      first
      | (exact absurd ‹_› hnpost)
      | (exact absurd ‹_› hninfl)
      | (rw [Prod.mk.injEq] at heq
         obtain ⟨rfl, hr2⟩ := heq
         have hrv : res.val = r := by rw [← hr2]
         rw [hrv])
  -- case23: out of bounds → identity
  case case23 =>
    intro d acc r hoob t' res heq
    rw [parseTail, dif_neg hoob] at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, hr2⟩ := heq
    have hrv : res.val = r := by rw [← hr2]
    rw [hrv]
  -- == SoundPrefix (parsePrefixBody), cases 24–32 =========================
  -- case24: names = [] → no parse
  case case24 =>
    intro d s interior trailing r heq
    unfold parsePrefixBody at heq; simp at heq
  -- case25: [n] (t::r), t = n, parse some → trailing child
  case case25 =>
    intro d t r c r₁ h₁ hpar ih1 interior trailing r' heq
    unfold parsePrefixBody at heq
    simp only [if_pos rfl, hpar, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    refine ⟨?_, rfl⟩
    have hh := ih1 c ⟨r₁, h₁⟩ hpar
    simp only [List.map_nil, List.nil_append, weavePrefix, List.cons_append, List.append_assoc]
    rw [show c.flatten ++ r₁ = r from hh]
  -- case26: [n] (t::r), t = n, parse none → no parse
  case case26 =>
    intro d t r hpar ih1 interior trailing r' heq
    unfold parsePrefixBody at heq; simp [if_pos rfl, hpar] at heq
  -- case27: [n] (t::r), t ≠ n → no parse
  case case27 =>
    intro d _n t r hnt interior trailing r' heq
    unfold parsePrefixBody at heq; simp [if_neg hnt] at heq
  -- case28: [n] [] → no parse
  case case28 =>
    intro d _n interior trailing r' heq
    unfold parsePrefixBody at heq; simp at heq
  -- case29: (n::n'::ns) (t::r), t = n, parse some, body some → cons
  case case29 =>
    intro d n' ns t r c r₁ h₁ hpar interior trailing r₂ h₂ hbody ih1 ihbody
      interior' trailing' r' heq
    unfold parsePrefixBody at heq
    simp only [if_pos rfl, hpar, hbody, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hc := ih1 c ⟨r₁, h₁⟩ hpar
    obtain ⟨hb, hlen'⟩ := ihbody interior trailing ⟨r₂, h₂⟩ hbody
    refine ⟨?_, by simp only [List.length_cons] at hlen' ⊢; omega⟩
    simp only [List.map_cons, List.cons_append, weavePrefix, List.append_assoc]
    rw [hb, hc]
  -- case30: (n::n'::ns) (t::r), t = n, parse some, body none → no parse
  case case30 =>
    intro d n' ns t r c r₁ h₁ hpar hbody ih1 ihbody interior' trailing' r' heq
    unfold parsePrefixBody at heq; simp [if_pos rfl, hpar, hbody] at heq
  -- case31: (n::n'::ns) (t::r), t = n, parse none → no parse
  case case31 =>
    intro d n' ns t r hpar ih1 interior' trailing' r' heq
    unfold parsePrefixBody at heq; simp [if_pos rfl, hpar] at heq
  -- case32: (n::n'::ns) (t::r), t ≠ n → no parse
  case case32 =>
    intro d n n' ns t r hnt interior' trailing' r' heq
    unfold parsePrefixBody at heq; simp [if_neg hnt] at heq
  -- case33: (n::n'::ns) [] → no parse
  case case33 =>
    intro d n n' ns interior' trailing' r' heq
    unfold parsePrefixBody at heq; simp at heq
  -- == SoundPostfix (parsePostfixBody), cases 34–43 =======================
  -- case33: names = [] → no parse
  case case34 =>
    intro s interior r heq
    unfold parsePostfixBody at heq; simp at heq
  -- case34: [n] (t::r), t = n → leading only, empty interior
  case case35 =>
    intro t r interior r' heq
    unfold parsePostfixBody at heq
    simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨fun lead => ?_, rfl⟩
    simp [weavePostfix]
  -- case35: [n] (t::r), t ≠ n → no parse
  case case36 =>
    intro _n t r hnt interior r' heq
    unfold parsePostfixBody at heq; simp [if_neg hnt] at heq
  -- case36: [n] [] → no parse
  case case37 =>
    intro _n interior r' heq
    unfold parsePostfixBody at heq; simp at heq
  -- case37: (n::n'::ns) (t::r), t = n, parse some, body some → cons
  case case38 =>
    intro n' ns t r c r₁ h₁ hpar interior r₂ h₂ hbody ih1 ihbody interior' r' heq
    unfold parsePostfixBody at heq
    simp only [if_pos rfl, hpar, hbody, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hc := ih1 c ⟨r₁, h₁⟩ hpar
    obtain ⟨hb, hlen'⟩ := ihbody interior ⟨r₂, h₂⟩ hbody
    refine ⟨fun lead => ?_, by simp only [List.length_cons] at hlen' ⊢; omega⟩
    calc weavePostfix (t :: n' :: ns) (lead :: (c :: interior).map (·.flatten)) ++ r₂
          = (lead ++ t :: weavePostfix (n' :: ns) (c.flatten :: interior.map (·.flatten))) ++ r₂ := by
              simp only [List.map_cons, weavePostfix]
        _ = lead ++ t :: (weavePostfix (n' :: ns) (c.flatten :: interior.map (·.flatten)) ++ r₂) := by
              simp [List.append_assoc]
        _ = lead ++ t :: (c.flatten ++ r₁) := by rw [hb c.flatten]
        _ = lead ++ t :: r := by rw [hc]
  -- case38: (n::n'::ns) (t::r), t = n, parse some, body none → no parse
  case case39 =>
    intro n' ns t r c r₁ h₁ hpar hbody ih1 ihbody interior' r' heq
    unfold parsePostfixBody at heq; simp [if_pos rfl, hpar, hbody] at heq
  -- case39: (n::n'::ns) (t::r), t = n, parse none → no parse
  case case40 =>
    intro n' ns t r hpar ih1 interior' r' heq
    unfold parsePostfixBody at heq; simp [if_pos rfl, hpar] at heq
  -- case40: (n::n'::ns) (t::r), t ≠ n → no parse
  case case41 =>
    intro n n' ns t r hnt interior' r' heq
    unfold parsePostfixBody at heq; simp [if_neg hnt] at heq
  -- case41: (n::n'::ns) [] → no parse
  case case42 =>
    intro n n' ns interior' r' heq
    unfold parsePostfixBody at heq; simp at heq
  -- == Sound2 (parseClosedBody), cases 44–52 ==============================
  case case43 => intro s cs r heq; unfold parseClosedBody at heq; simp at heq
  case case44 =>
    intro t r cs r' heq
    unfold parseClosedBody at heq
    simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨by simp [weaveClosed], rfl⟩
  case case45 => intro _n t r hnt cs r' heq; unfold parseClosedBody at heq; simp [if_neg hnt] at heq
  case case46 => intro _n cs r heq; unfold parseClosedBody at heq; simp at heq
  case case47 =>
    intro n' ns t r c r₁ h₁ hpc cs r₂ h₂ hpb ih1 ih2 cs' r' heq
    unfold parseClosedBody at heq
    simp only [if_pos rfl, hpc, hpb, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hc := ih1 c ⟨r₁, h₁⟩ hpc
    obtain ⟨hbody, hlen'⟩ := ih2 cs ⟨r₂, h₂⟩ hpb
    refine ⟨?_, by simp only [List.length_cons] at hlen' ⊢; omega⟩
    simp only [List.map_cons, weaveClosed, List.cons_append, List.append_assoc]
    rw [hbody, hc]
  case case48 =>
    intro n' ns t r c r₁ h₁ hpc hpb _ih1 _ih2 cs' r' heq
    unfold parseClosedBody at heq; simp [if_pos rfl, hpc, hpb] at heq
  case case49 =>
    intro n' ns t r hpc _ih1 cs' r' heq
    unfold parseClosedBody at heq; simp [if_pos rfl, hpc] at heq
  case case50 =>
    intro n n' ns t r hnt cs' r' heq; unfold parseClosedBody at heq; simp [if_neg hnt] at heq
  case case51 =>
    intro n n' ns cs' r' heq; unfold parseClosedBody at heq; simp at heq

/-- **Parse soundness** (the round-trip direction `parse ⊇ flatten`): for
*every* fixity, whatever `parse` returns flattens back to a prefix of the
input. A direct corollary of `parse_sound_all`. -/
theorem parse_sound (G : Grammar) (d : Nat) (s : List String)
    (t : Tree G d) (r : Rest s) (h : parse G d s = some (t, r)) :
    t.flatten ++ r.val = s :=
  parse_sound_all G d s t r h

end LambdaLab.Parser.Mixfix2
