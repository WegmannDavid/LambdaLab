import LambdaLab.Parser.Mixfix.Tree

/-!
# Mixfix parser (total, subtype-based, Tree-producing)

A total recursive-descent parser. The primary function `parseTree`
produces a `Tree α` together with the leftover tokens; the value-level
`parse` is derived from it via `Tree.eval`.

Termination is via subtypes: every parsing function returns
`Option (β × { rest : List String // rest.length < input.length })`,
so each recursive call comes with a proof that the input strictly
shrinks. Mutual termination is via lex `(input.length, priority)`.

`Parser β` (the user-facing sub-parser type) keeps its simple
`run : List String → Option (β × List String)` signature; the parser
checks at the call site that any sub-parser actually consumed at least
one token (via `runParser`), failing otherwise.

All four fixities are supported. The flow is:
* `parseHead` parses an atom or a closed/prefix operator (detectable by
  the first input token).
* `tryTail` wraps an already-parsed head with a postfix or infix
  operator (whose leading hole is the head). Postfix's tail walk
  reduces to `parseTreeClosedSeq` on `op.holes.tail`; infix's reduces
  to `parseTreePrefixSeq`.
* `tryTailLoop` repeatedly applies `tryTail` so multiple trailing
  operators can chain.
* The top-level `parseTree` is `parseHead` followed by `tryTailLoop`.

Postfix/infix require `op.holes.head = .recurse` (the leading hole is
recursive). Other shapes are rejected.
-/

namespace LambdaLab.Parser.Mixfix

/-! ## Token-level helpers -/

/-- Match a literal token at the head of an input list. -/
def matchToken (tok : String) : ∀ (input : List String),
    Option { rest : List String // rest.length < input.length }
  | []        => none
  | t :: rest =>
      if t == tok then
        some ⟨rest, Nat.lt_succ_self _⟩
      else
        none

/-- Whether `tok` could start an expression in `g`. Used to gate
juxtaposition: `f )` shouldn't juxtapose because `)` isn't an
expression starter. A token can start an expression if either it's not
mentioned in any operator's name-parts (a free atom), or it is the
first name-part of some closed/prefix operator. -/
def canStartExpr {α : Type} (g : Grammar α) (tok : String) : Bool :=
  let isInAnyNameParts :=
    g.levels.flatten.any (fun op => op.nameParts.contains tok)
  let isFirstOfHeadOp :=
    g.levels.flatten.any (fun op =>
      (op.fixity matches .closed | .prefix) &&
      op.nameParts.head?.elim false (· == tok))
  ¬ isInAnyNameParts || isFirstOfHeadOp

/-- Run a user-supplied sub-parser, requiring that it consumes at least
one token. If the sub-parser returns the same (or longer) input, treat
it as a parse failure. -/
def runParser {β : Type} (subP : Parser β) (input : List String) :
    Option (β × { rest : List String // rest.length < input.length }) :=
  match subP.run input with
  | none => none
  | some (val, rest) =>
      if h : rest.length < input.length then
        some (val, ⟨rest, h⟩)
      else
        none

/-! ## Re-usable sub-parsers -/

/-- A sub-parser that consumes exactly one token as a `String`. Useful
for binders that bind a variable name (e.g. `λ x : τ . body`), and for
the vernacular's `def NAME` slot. (This will eventually want a
keyword-excluding variant; for now any token is accepted.) -/
def stringParser : Parser String where
  run := fun input =>
    match input with
    | []        => none
    | t :: rest => some (t, rest)
  printer := fun s => [s]

/-- Atom fallback: take the first token and wrap it as `Tree.atom`. -/
def atomFallbackTree {α : Type} : ∀ (input : List String),
    Option (Tree α × { rest : List String // rest.length < input.length })
  | []        => none
  | t :: rest => some (.atom t, ⟨rest, Nat.lt_succ_self _⟩)

/-! ## Tree-producing parser -/

mutual
  /-- Try parsing the input as a head operator (closed or prefix). -/
  def tryOp {α : Type} (g : Grammar α) (input : List String)
      (op : Operator α) :
      Option (Tree α × { rest : List String // rest.length < input.length }) :=
    match op.fixity with
    | .closed =>
        match parseTreeClosedSeq g op.nameParts op.holes input with
        | some (cs, rest) => some (.node op cs, rest)
        | none            => none
    | .prefix =>
        match parseTreePrefixSeq g op.nameParts op.holes input with
        | some (cs, rest) => some (.node op cs, rest)
        | none            => none
    | _       => none
  termination_by (input.length, 1)

  /-- Try wrapping an already-parsed head with a postfix or infix
  operator. Requires `op.holes.head = .recurse` so the head fits the
  leading hole as a recursive child. -/
  def tryTail {α : Type} (g : Grammar α) (head : Tree α)
      (input : List String) (op : Operator α) :
      Option (Tree α × { rest : List String // rest.length < input.length }) :=
    match h_holes : op.holes, op.fixity with
    | .recurse :: tailHoles, .postfix =>
        match parseTreeClosedSeq g op.nameParts tailHoles input with
        | some (cs, rest) =>
            some (.node op (h_holes ▸ Children.consRec head cs), rest)
        | none => none
    | .recurse :: tailHoles, .infix _ =>
        match parseTreePrefixSeq g op.nameParts tailHoles input with
        | some (cs, rest) =>
            some (.node op (h_holes ▸ Children.consRec head cs), rest)
        | none => none
    | _, _ => none
  termination_by (input.length, 1)

  /-- Parse a head expression: an atom or a closed/prefix operator. -/
  def parseHead {α : Type} (g : Grammar α) (input : List String) :
      Option (Tree α × { rest : List String // rest.length < input.length }) :=
    match g.levels.flatten.findSome? (tryOp g input) with
    | some r => some r
    | none   => atomFallbackTree input
  termination_by (input.length, 2)

  /-- Repeatedly apply `tryTail` (and juxtaposition, if enabled) to wrap
  `head` with as many trailing operators / applications as match.
  Returns the final tree and any unconsumed tokens. Always returns at
  least the unwrapped head. -/
  def tryTailLoop {α : Type} (g : Grammar α) (head : Tree α)
      (input : List String) :
      Tree α × { rest : List String // rest.length ≤ input.length } :=
    match g.levels.flatten.findSome? (tryTail g head input) with
    | some (newHead, ⟨rest, hR⟩) =>
        let next := tryTailLoop g newHead rest
        ⟨next.fst,
          ⟨next.snd.val, by have := next.snd.property; omega⟩⟩
    | none =>
        match g.juxtBuild with
        | none => ⟨head, ⟨input, Nat.le_refl _⟩⟩
        | some f =>
            match h_inp : input.head? with
            | none => ⟨head, ⟨input, Nat.le_refl _⟩⟩
            | some tok =>
                if canStartExpr g tok then
                  match parseHead g input with
                  | none => ⟨head, ⟨input, Nat.le_refl _⟩⟩
                  | some (next, ⟨rest, hR⟩) =>
                      let further := tryTailLoop g (.app f head next) rest
                      ⟨further.fst,
                       ⟨further.snd.val,
                        by have := further.snd.property; omega⟩⟩
                else ⟨head, ⟨input, Nat.le_refl _⟩⟩
  termination_by (input.length, 3)

  /-- Parse a token list into a parse tree. Parses a head, then applies
  any trailing postfix/infix operators. Always consumes at least one
  token on success (via `parseHead`). -/
  def parseTree {α : Type} (g : Grammar α) (input : List String) :
      Option (Tree α × { rest : List String // rest.length < input.length }) :=
    match parseHead g input with
    | none => none
    | some (head, ⟨rest, hR⟩) =>
        let result := tryTailLoop g head rest
        some (result.fst,
              ⟨result.snd.val, by have := result.snd.property; omega⟩)
  termination_by (input.length, 4)

  /-- Walk a closed operator's interleaved name-parts and holes, building
  a `Children α hs` value. -/
  def parseTreeClosedSeq {α : Type} (g : Grammar α) :
      List String → ∀ (hs : List (HoleSpec α)),
        ∀ (input : List String),
        Option (Children α hs ×
          { rest : List String // rest.length < input.length })
    | [last],    [],                input =>
        match matchToken last input with
        | none              => none
        | some ⟨rest, hR⟩  => some (.nil, ⟨rest, hR⟩)
    | np :: nps, .recurse :: hs,    input =>
        match matchToken np input with
        | none              => none
        | some ⟨rest, hR⟩  =>
            match parseTree g rest with
            | none                       => none
            | some (subTree, ⟨rest', hR'⟩) =>
                match parseTreeClosedSeq g nps hs rest' with
                | none                    => none
                | some (cs, ⟨rest'', hR''⟩) =>
                    some (.consRec subTree cs, ⟨rest'', by omega⟩)
    | np :: nps, .sub subP :: hs, input =>
        match matchToken np input with
        | none              => none
        | some ⟨rest, hR⟩  =>
            match runParser subP rest with
            | none                    => none
            | some (val, ⟨rest', hR'⟩) =>
                match parseTreeClosedSeq g nps hs rest' with
                | none                    => none
                | some (cs, ⟨rest'', hR''⟩) =>
                    some (.consSub val cs, ⟨rest'', by omega⟩)
    | _,         _,                 _     => none
  termination_by _ _ input => (input.length, 0)

  /-- Walk a prefix operator's interleaved name-parts and holes. A prefix
  operator with `n` name-parts has `n` holes (one trailing each name).
  Base case: a single name + a single hole. -/
  def parseTreePrefixSeq {α : Type} (g : Grammar α) :
      List String → ∀ (hs : List (HoleSpec α)),
        ∀ (input : List String),
        Option (Children α hs ×
          { rest : List String // rest.length < input.length })
    | [name],    [.recurse],          input =>
        match matchToken name input with
        | none              => none
        | some ⟨rest, hR⟩  =>
            match parseTree g rest with
            | none                    => none
            | some (tree, ⟨rest', hR'⟩) =>
                some (.consRec tree .nil, ⟨rest', by omega⟩)
    | [name],    [.sub subP],         input =>
        match matchToken name input with
        | none              => none
        | some ⟨rest, hR⟩  =>
            match runParser subP rest with
            | none                   => none
            | some (val, ⟨rest', hR'⟩) =>
                some (.consSub val .nil, ⟨rest', by omega⟩)
    | np :: nps, .recurse :: hs,      input =>
        match matchToken np input with
        | none              => none
        | some ⟨rest, hR⟩  =>
            match parseTree g rest with
            | none                       => none
            | some (subTree, ⟨rest', hR'⟩) =>
                match parseTreePrefixSeq g nps hs rest' with
                | none                    => none
                | some (cs, ⟨rest'', hR''⟩) =>
                    some (.consRec subTree cs, ⟨rest'', by omega⟩)
    | np :: nps, .sub subP :: hs,   input =>
        match matchToken np input with
        | none              => none
        | some ⟨rest, hR⟩  =>
            match runParser subP rest with
            | none                    => none
            | some (val, ⟨rest', hR'⟩) =>
                match parseTreePrefixSeq g nps hs rest' with
                | none                    => none
                | some (cs, ⟨rest'', hR''⟩) =>
                    some (.consSub val cs, ⟨rest'', by omega⟩)
    | _,         _,                   _     => none
  termination_by _ _ input => (input.length, 0)
end

/-! ## Top-level entry points -/

/-- Parse a token list, producing a value of the grammar's result type
via `Tree.eval`. -/
def parse {α : Type} (g : Grammar α) (input : List String) :
    Option (α × { rest : List String // rest.length < input.length }) :=
  match parseTree g input with
  | none              => none
  | some (t, rest)    => some (Tree.eval g t, rest)

/-- Parse a complete token list. Succeeds only if the parse consumes
every token. -/
def parseAll {α : Type} (g : Grammar α) (input : List String) : Option α :=
  match parseTree g input with
  | some (t, ⟨[], _⟩) => some (Tree.eval g t)
  | _                 => none

/-- Like `parseAll` but returns the parse tree as well. -/
def parseAllTree {α : Type} (g : Grammar α) (input : List String) :
    Option (Tree α) :=
  match parseTree g input with
  | some (t, ⟨[], _⟩) => some t
  | _                 => none

end LambdaLab.Parser.Mixfix
