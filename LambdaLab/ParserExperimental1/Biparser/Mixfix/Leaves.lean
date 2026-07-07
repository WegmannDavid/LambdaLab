import LambdaLab.ParserExperimental1.Biparser.Mixfix.Basic
import LambdaLab.ParserExperimental1.Biparser.Example

/-!
# Combinator leaves for the mixfix grammar

Every token/gap the grammar uses is a **combinator**, so its round-trip is discharged by
that combinator's own `parse_complete` (composed by `seq`). All name/variable/operator
tokens are single characters (`tok`); every gap is `spaces1` (the verified ≥1-space
biparser), pre-composed with its adjacent token via `seq` (`lpGap = seq lparen spaces1`,
…) so that in the parser each recursive call sits one `flatMap` deep.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

def varTok (G : Grammar) : Biparser Char Unit {c : Char // G.isVar c = true} :=
  tok (fun c => G.isVar c)
def lparen : Biparser Char Unit {c : Char // (c == '(') = true} := tok (· == '(')
def rparen : Biparser Char Unit {c : Char // (c == ')') = true} := tok (· == ')')
def opTok (G : Grammar) (k : Nat) (hk : k < G.ops.length) :
    Biparser Char Unit {c : Char // (c == G.opChar k hk) = true} := tok (· == G.opChar k hk)

/-- `"(" ++ gap`. -/
def lpGap := seq lparen spaces1
/-- `gap ++ ")"`. -/
def gapRp := seq spaces1 rparen
/-- `gap ++ opₖ ++ gap` (an infix operator with its surrounding gaps). -/
def gapOpGap (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq spaces1 (seq (opTok G k hk) spaces1)
/-- `opₖ ++ gap` (a prefix operator with its trailing gap). -/
def opGap (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq (opTok G k hk) spaces1
/-- `gap ++ opₖ` (a postfix operator with its leading gap). -/
def gapOp (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq spaces1 (opTok G k hk)

/-- The bracket / operator token values used by `render`. -/
def lpVal : {c : Char // (c == '(') = true} := ⟨'(', by decide⟩
def rpVal : {c : Char // (c == ')') = true} := ⟨')', by decide⟩
def opVal (G : Grammar) (k : Nat) (hk : k < G.ops.length) :
    {c : Char // (c == G.opChar k hk) = true} := ⟨G.opChar k hk, beq_self_eq_true _⟩

end LambdaLab.ParserExperimental1.Mixfix
