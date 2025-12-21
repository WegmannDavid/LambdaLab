import LambdaLab.Mixfix.Closed

open Std.Internal Parsec String

inductive Open (A : Type) where
| prefx  :          Closed A → Hole A → Open A
| postfx : Hole A → Closed A          → Open A
| infxl  :          Closed A → Hole A → Open A
| infx   : Hole A → Closed A → Hole A → Open A
| infxr  : Hole A → Closed A          → Open A




def arity (p : Open A) :=
  match p with
  | .prefx    c k =>              carity c (holeType k → A)
  | .postfx h c   => holeType h → carity c               A
  | .infxl    c k => A          → carity c (holeType k → A)
  | .infx   h c k => holeType h → carity c (holeType k → A)
  | .infxr  h c   => holeType h → carity c (A          → A)



partial def pOpen (pExpr : Parser A) (pUp : Parser A) (m : Open A) (t : arity m) : Parser A :=
  match m with
  | .prefx    c k => do
      let c ← pClosed pExpr c t
      let r ← pHole pExpr k
      return (c r)
  | .postfx h c   => do
      let l ← pHole pUp h
      pClosed pExpr c (t l)
  | .infxl    c k =>
    let rec helper l :=
      (attempt (do let i ← pClosed pExpr c (t l)
                   let r ← pHole pUp k
                   helper (i r))) <|> return l
    do
      let l ← pUp
      helper l
  | .infx   h c k => do
      let l ← pHole pUp h
      let i ← pClosed pExpr c (t l)
      let r ← pHole pUp k
      return (i r)
  | .infxr  h c  => do
      let l ← pHole pUp h
      let i ← pClosed pExpr c (t l)
      let r ← (attempt (pOpen pExpr pUp (.infxr h c) t)) <|> pUp
      return (i r)

structure OpenNotation (A : Type) where
  mfx : Open A
  term : arity mfx

def pOpenNotation (pExpr : Parser A) (pUp : Parser A) (n : OpenNotation A) : Parser A := pOpen pExpr pUp n.mfx n.term
