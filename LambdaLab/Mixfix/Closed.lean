import LambdaLab.Mixfix.Base

open Std.Internal Parsec String

inductive Hole (A : Type) where
| expr  : Hole A
| other : Parser B → Hole A

def holeType (h : Hole A) :=
  match h with
  |  Hole.expr      => A
  | @Hole.other _ B _ => B

inductive Closed (A : Type) where
| last  : String → Closed A
| hole  : String → Hole A → Closed A → Closed A

namespace Closed
  def expr  (s : String)                 (c : Closed A) : Closed A := .hole s .expr c
  def other (s : String) (pB : Parser B) (c : Closed A) : Closed A := .hole s (.other pB) c
end Closed

def carity (c : Closed A) (R : Type) :=
    match c with
    | .last _      => R
    | .hole _  h c' => holeType h → carity c' R

structure ClosedNotation (A : Type) where
  c : Closed A
  term : carity c A

def pHole (pA : Parser A) (h : Hole A) : Parser (holeType h) :=
  match h with
  | .expr     => pA
  | .other pB => lexeme pB

def pClosed (pA : Parser A) (c : Closed A) (t : carity c R) : Parser R :=
  match c with
  | .last s => pSymbol s *> return t
  | .hole s h c' => do
    let _ ← pSymbol s
    let x ← pHole pA h
    pClosed pA c' (t x)

def pClosedNotation (pA : Parser A) (c : ClosedNotation A) : Parser A := pClosed pA c.c c.term
