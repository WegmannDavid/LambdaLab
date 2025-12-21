import LambdaLab.Stlc.Parser.Parse
import LambdaLab.Stlc.Elaborator.Elaborate

import LambdaLab.Stlc.Parser.Vernacular

import LambdaLab.Stlc.Vernacular

def fromParserTy (α : Stlc.Parser.Ty) (n : Nat) : Ty × Nat :=
  match α with
  | .inf      => ⟨ .var n, n + 1 ⟩
  | .arr α β  =>
    let ⟨ α, n'  ⟩ := fromParserTy α n
    let ⟨ β, n'' ⟩ := fromParserTy β n'
    ⟨ .arr α β, n'' ⟩
  | .atm s    => ⟨ .atm s, n ⟩

def fromParserTm (t : Stlc.Parser.Tm) (n : Nat) : Tm × Nat :=
  match t with
  | .var x    => ⟨ .var x, n ⟩
  | .app t s  =>
    let ⟨ t', n'  ⟩ := fromParserTm t n
    let ⟨ s', n'' ⟩ := fromParserTm s n'
    ⟨ .app t' s', n'' ⟩
  | .abs x α t =>
    let ⟨ α', n' ⟩  := fromParserTy α n
    let ⟨ t', n'' ⟩ := fromParserTm t n'
    ⟨ .abs x α' t', n'' ⟩

def fromParserDeclaration (d : Stlc.Parser.Declaration) (n : Nat) : Declaration × Nat :=
  match d with
  | ⟨ s, α, t ⟩ =>
    let ⟨ α', n'  ⟩ := fromParserTy α n
    let ⟨ t', n'' ⟩ := fromParserTm t n'
    ⟨ ⟨ s, α', t' ⟩ , n'' ⟩

def fromParserVernacular (v : Stlc.Parser.Vernacular) (n : Nat) : Vernacular × Nat :=
  match v with
  | []    => ⟨ [], 0 ⟩
  | d::ds =>
    let ⟨ d', n'  ⟩ := fromParserDeclaration d n
    let ⟨ ds, n'' ⟩ := fromParserVernacular ds n'
    ⟨ d'::ds, n'' ⟩

def compile (s : String) : Except String (Vernacular) := do
  let parsed ← parseVernacular.run s
  let ⟨ initialized, _ ⟩ := fromParserVernacular parsed 0
  let ⟨ compiled, _ ⟩ ← elaborateVernacular ∅ sorry initialized
  return compiled
