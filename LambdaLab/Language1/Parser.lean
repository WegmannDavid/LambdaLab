import LambdaLab.Language1.Vernacular

/-!
# Quick-and-dirty vernacular parser (parse only, unverified)

`Language.parser` parses a nonempty run of `def NAME : TYPE := BODY` commands,
delegating `TYPE` to `L.pTy` and `BODY` to `L.pTm` and taking the first parse of
each. `render` is a naive fully-spelled-out printer; `complete` (the round-trip)
is left as `sorry` — this is scaffolding, not a verified parser.
-/

namespace LambdaLab.Language1

open LambdaLab.ParserOld

/-- Consume the exact token `t` at the head of `l` (if present). Returns a
`RightSublist` of the *given* `l`, so callers compose with `.trans` cleanly. -/
private def expectTok (t : Token) : (l : List Token) → Option (RightSublist l)
  | []          => none
  | x :: rest   => if x = t then some (RightSublist.cons x rest) else none

/-- Consume any single token at the head of `l`. -/
private def anyTok : (l : List Token) → Option (Token × RightSublist l)
  | []        => none
  | x :: rest => some (x, RightSublist.cons x rest)

/-- Parse one `def NAME : TYPE := BODY` command: match the keywords, read the
name, and take the first parse of `L.pTy` / `L.pTm` for the type and body. The
leftover is threaded through `RightSublist.trans` so the whole thing is a proper
`RightSublist input`. -/
private def parseCmd (L : Language) (input : List Token) :
    Option (Command L × RightSublist input) :=
  match expectTok "def" input with
  | none      => none
  | some sDef =>
    match anyTok sDef.list with
    | none              => none
    | some (name, sName) =>
      let s1 := sDef.trans sName
      match expectTok ":" s1.list with
      | none        => none
      | some sColon =>
        let s2 := s1.trans sColon
        match (L.pTy.parse s2.list).head? with
        | none        => none
        | some (τ, sTy) =>
          let s3 := s2.trans sTy
          match expectTok ":=" s3.list with
          | none         => none
          | some sAssign =>
            let s4 := s3.trans sAssign
            match (L.pTm.parse s4.list).head? with
            | none            => none
            | some (body, sBody) =>
              some (Command.decl name τ body, s4.trans sBody)

/-- Parse a nonempty run of commands, greedily. Each command consumes at least
the `def` token, so the leftover strictly shrinks and the recursion terminates. -/
private def parseCmds (L : Language) (input : List Token) :
    Option (Program L × RightSublist input) :=
  match parseCmd L input with
  | none         => none
  | some (c, sc) =>
    match parseCmds L sc.list with
    | none          => some ([c], sc)
    | some (cs, scs) => some (c :: cs, sc.trans scs)
  termination_by input.length
  decreasing_by exact sc.length_lt

/-- Render one command back to tokens, fully spelled out. -/
private def renderCmd (L : Language) : Command L → List Token
  | .decl name τ body =>
      "def" :: name :: ":" :: (L.pTy.render τ ++ ":=" :: L.pTm.render body)

/-- The quick-and-dirty vernacular parser: `parse` a nonempty run of commands,
`render` naively, round-trip left unproved. -/
def Language.parser (L : Language) : TruncatingParser Token (Program L) where
  parse input := (parseCmds L input).toList
  render prog := (prog.map (renderCmd L)).flatten
  complete := by sorry

end LambdaLab.Language1
