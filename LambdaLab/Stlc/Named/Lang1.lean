import LambdaLab.Stlc.Named.Basic
import LambdaLab.Language1.Basic

/-!
# Quick-and-dirty STLC instance of `Language1.Language`

The mixfix-based surface parser (`Stlc/Named/Syntax/`) is currently un-ported to
the multi-entry `Grammar` and does not build, so this file **hand-rolls** the two
payload parsers by recursive descent instead of going through the grammar:

* `pTm` — terms: variables, application by juxtaposition (left-assoc), parenthesized
  groups, and `\lambda x . body`. Every binder gets the annotation `Ty.mvar 0`
  (fresh-var handling deferred — all zero for now).
* `pTy` — types: `*` (base), `->` (right-assoc arrow), parenthesized groups.

Both are `partial` (no termination proof), `parse`-only, `render` naive, and the
round-trip `complete` is `sorry`. This is scaffolding to exercise the vernacular
`Language.parser`, not a verified front end.
-/

namespace LambdaLab.Stlc.Named

open LambdaLab.Parser
open LambdaLab.Language1

/-- Tokens that may not be read as a term variable / binder name: the term
delimiters and the vernacular keywords (so a body stops at the next `def`). -/
def tmReserved : List Token := ["(", ")", "\\lambda", ".", "def", ":", ":="]

/-! ## Shared consumption helpers (return a `RightSublist` of the *given* list) -/

/-- Consume the exact token `t` at the head. -/
private def eat (t : Token) : (l : List Token) → Option (RightSublist l)
  | []        => none
  | x :: rest => if x = t then some (RightSublist.cons x rest) else none

/-- Consume any single non-reserved token (a variable / name). -/
private def eatVar (reserved : List Token) : (l : List Token) → Option (Token × RightSublist l)
  | []        => none
  | x :: rest => if x ∈ reserved then none else some (x, RightSublist.cons x rest)

/-! ## Term parser -/

mutual
  /-- An atom: a parenthesized term or a single variable. -/
  private partial def parseAtom : (l : List Token) → Option (Term × RightSublist l)
    | "(" :: rest =>
        let s0 := RightSublist.cons "(" rest
        match parseTerm s0.list with
        | none         => none
        | some (t, st) =>
            let s1 := s0.trans st
            match eat ")" s1.list with
            | none    => none
            | some sc => some (t, s1.trans sc)
    | l =>
        match eatVar tmReserved l with
        | none          => none
        | some (x, sx)  => some (Term.var x, sx)

  /-- An application: one atom, then greedily fold further atoms (left-assoc). -/
  private partial def parseApp (l : List Token) : Option (Term × RightSublist l) :=
    match parseAtom l with
    | none         => none
    | some (f, sf) => parseAppLoop f sf

  /-- Fold zero or more argument atoms onto `acc`. Always succeeds (`some`); the
  `Option` is only there to make the dependent return type inhabited for `partial`. -/
  private partial def parseAppLoop (acc : Term) {l : List Token} (s : RightSublist l) :
      Option (Term × RightSublist l) :=
    match parseAtom s.list with
    | none          => some (acc, s)
    | some (x, sx)  => parseAppLoop (Term.app acc x) (s.trans sx)

  /-- A term (loosest): a lambda, or an application. -/
  private partial def parseTerm : (l : List Token) → Option (Term × RightSublist l)
    | "\\lambda" :: rest =>
        let s0 := RightSublist.cons "\\lambda" rest
        match eatVar tmReserved s0.list with
        | none              => none
        | some (name, sName) =>
            let s1 := s0.trans sName
            match eat "." s1.list with
            | none      => none
            | some sDot =>
                let s2 := s1.trans sDot
                match parseTerm s2.list with
                | none            => none
                | some (body, sB) => some (Term.lam name (Ty.mvar 0) body, s2.trans sB)
    | l => parseApp l
end

/-- Naive canonical printer: variables bare, applications and lambdas fully
parenthesized (annotation dropped). -/
private def renderTm : Term → List Token
  | .var x        => [x]
  | .app f a      => ["("] ++ renderTm f ++ renderTm a ++ [")"]
  | .lam x _ body => ["(", "\\lambda", x, "."] ++ renderTm body ++ [")"]

/-- The STLC term parser (parse-only, unverified). -/
def pTerm : TruncatingParser Token Term where
  parse l  := (parseTerm l).toList
  render   := renderTm
  complete := by sorry

/-! ## Type parser -/

mutual
  /-- A type atom: `*` (base) or a parenthesized type. -/
  private partial def parseTyAtom : (l : List Token) → Option (Ty × RightSublist l)
    | "*" :: rest => some (Ty.base, RightSublist.cons "*" rest)
    | "(" :: rest =>
        let s0 := RightSublist.cons "(" rest
        match parseTyArrow s0.list with
        | none         => none
        | some (t, st) =>
            let s1 := s0.trans st
            match eat ")" s1.list with
            | none    => none
            | some sc => some (t, s1.trans sc)
    | _ => none

  /-- An arrow chain `A -> B -> …`, right-associative. -/
  private partial def parseTyArrow (l : List Token) : Option (Ty × RightSublist l) :=
    match parseTyAtom l with
    | none         => none
    | some (a, sa) =>
        match eat "->" sa.list with
        | none      => some (a, sa)
        | some sArr =>
            let s1 := sa.trans sArr
            match parseTyArrow s1.list with
            | none         => some (a, sa)
            | some (b, sb) => some (Ty.arrow a b, s1.trans sb)
end

/-- Naive canonical printer: `*`, arrows fully parenthesized, mvars as `?n`. -/
private def renderTy : Ty → List Token
  | .base      => ["*"]
  | .arrow a b => ["("] ++ renderTy a ++ ["->"] ++ renderTy b ++ [")"]
  | .mvar n    => ["?" ++ toString n]

/-- The STLC type parser (parse-only, unverified). -/
def pType : TruncatingParser Token Ty where
  parse l  := (parseTyArrow l).toList
  render   := renderTy
  complete := by sorry

/-! ## The instance -/

/-- STLC as a `Language1.Language` (quick and dirty, parse only). -/
def stlcLang : Language where
  Tm   := Term
  Ty   := Ty
  pTm  := pTerm
  pTy  := pType

end LambdaLab.Stlc.Named
