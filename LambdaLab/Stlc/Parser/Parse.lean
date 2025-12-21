import LambdaLab.Mixfix.Parser
import LambdaLab.Stlc.Parser.Ty
import LambdaLab.Stlc.Parser.Tm
import LambdaLab.Stlc.Parser.Vernacular

open Std.Internal Parsec String Stlc.Parser

def alphaHole {α} : Hole α := (.other (pAlpha (λ _ ↦ false)))

def tyAtmNotation : ClosedNotation Ty where
  c := .hole "" alphaHole (.last "")
  term := Ty.atm

def tyArrowNotation : OpenNotation Ty where
  mfx := .infxr .expr (.last "→")
  term := Ty.arr

def tyInfNotation : ClosedNotation Ty where
  c := (.last "_")
  term := Ty.inf

def tyGrammar : MixfixGrammar Ty where
  precedence := [tyArrowNotation]
  closed     := [parentheses, tyInfNotation, tyAtmNotation]
  juxta      := none

def parseTy := pExpr tyGrammar


def tmVarNotation : ClosedNotation Tm where
  c := .hole "" alphaHole (.last "")
  term := Tm.var

def tmAbsNotation : OpenNotation Tm where
  mfx := .prefx (.hole "λ" alphaHole (.hole ":" (.other parseTy) (.last "."))) .expr
  term := Tm.abs

def tmAbsInfNotation : OpenNotation Tm where
  mfx := .prefx (.hole "λ" alphaHole (.last ".")) .expr
  term := λ x t ↦ Tm.abs x .inf t

def tmGrammar : MixfixGrammar Tm where
  precedence := [tmAbsNotation, tmAbsInfNotation]
  closed     := [parentheses, tmVarNotation]
  juxta      := some .app

def parseTm := pExpr tmGrammar

def declarationNotation : OpenNotation Vernacular where
  mfx := .prefx (.hole "def" alphaHole (.hole ":" (.other parseTy) (.hole ":=" (.other parseTm) (.last ";")))) .expr
  term := (λ s α t v ↦ ⟨ s, α, t ⟩::v)

def declarationNotationInf : OpenNotation Vernacular where
  mfx := .prefx (.hole "def" alphaHole (.hole ":=" (.other parseTm) (.last ";"))) .expr
  term := (λ s t v ↦ ⟨ s, .inf, t ⟩::v)

def endNotation : ClosedNotation Vernacular where
  c := (.last "")
  term := []

def vernacularGrammar : MixfixGrammar Vernacular where
  precedence := [declarationNotation, declarationNotationInf]
  closed     := [endNotation]
  juxta      := none

def parseVernacular := pExpr vernacularGrammar
