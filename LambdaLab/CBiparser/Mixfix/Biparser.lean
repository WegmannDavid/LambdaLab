import LambdaLab.CBiparser.Mixfix.Parse
import LambdaLab.CBiparser.Indexed

/-!
# The mixfix biparser

Assembling the pieces into a `CBiparser` over the **token** alphabet:

* `parse` — the mutual recursion from `Parse.lean` (well-founded on
  `(tkns.length, Level.measure l, phase)`), re-wrapped so its leftover is `CBiparser`'s
  strict-suffix subtype. `RightSublist` and that subtype are the *same thing* — a list plus a
  proof it is strictly shorter — so the adapter is a one-liner.
* `print` — **`Expr.flatten`**, and nothing else. The tree already flattens to a token list, so
  the printer side is free. Source and value are both `Expr`, i.e. an *aligned* biparser.

## The indices

**FIRST is free.** `firstOk` is a purely negative claim ("outside FIRST, I fail"), so the
weakest possible FIRST — `⊤` — makes it **vacuous**: there is no token outside `⊤`, so there is
nothing to prove. And `Language1`'s interface asks for exactly `anyTok`, so nothing is lost.
This is the same reason we could delete `tyFirst`/`tmFirst` from `Language`.

**FOLLOW is where all the content is.** It must be a set of tokens at which the parser
*provably stops*. The greedy parser continues on anything that could extend an expression:

* a **variable** token (juxtaposition: `f x`),
* an **infix/postfix** operator token (`a + b`),
* the head of a **closed/prefix** operator (`f (x)` — `(` starts an operand).

So FOLLOW is the complement of those. Note what this forces on a grammar plugged into
`Language1`: its `isVar` **must not accept `def` or `:=`**, or the term parser would read the
next command's keyword as a variable and juxtapose it into the term. That requirement is not
bureaucratic — it *is* the statement that the vernacular is unambiguous, and it is exactly what
`ok` will need.
-/

namespace LambdaLab.CBiparser.Mixfix

open LambdaLab.CBiparser

variable {G : Grammar}

/-- The parser, re-wrapped for `CBiparser`. `RightSublist` *is* the strict-suffix subtype. -/
def parseCB (e : G.Ent) (l : Level (G.entry e)) (input : List (Token G.isSep)) :
    Option (Expr G e l × { r : List (Token G.isSep) // r.length < input.length }) :=
  (parseExpr e l input).map (fun (t, s) => (t, ⟨s.list, s.lt⟩))

/-- **The mixfix biparser.** Aligned: source and value are both the tree. `print` is `flatten`. -/
def biparser (G : Grammar) (e : G.Ent) (l : Level (G.entry e)) :
    CBiparser (Token G.isSep) (Expr G e l) (Expr G e l) where
  parse := parseCB e l
  print := fun t => (t, t.flatten)

/-! ## FIRST — vacuous, hence free -/

/-- The weakest FIRST: everything. `firstOk` is then unprovable-to-violate. -/
abbrev anyTok : Token G.isSep → Bool := fun _ => true

theorem firstOk_any (e : G.Ent) (l : Level (G.entry e))
    (t : Token G.isSep) (rest : List (Token G.isSep)) (h : anyTok (G := G) t = false) :
    (biparser G e l).run (t :: rest) = none := by
  simp [anyTok] at h

/-! ## FOLLOW — the tokens at which the parser provably stops

A token **continues** an expression if it can start an operand (a variable, or the head of a
non-left-recursive operator) or is an operator's connective. FOLLOW is the complement. -/

/-- Can this token **start an operand** of entry `e`?

A variable can. So can the leading token of an operator that does *not* begin with a hole
(`closed`, `prefx`) — `(` starts a parenthesised operand, so in `f (x)` it continues the
juxtaposition rather than terminating `f`. -/
def startsOperand (e : G.Ent) (t : Token G.isSep) : Bool :=
  (G.entry e).isVar t ||
    (G.entry e).ops.any (fun o =>
      let op := (G.entry e).operator o
      !op.startsWithHole &&
        (match op.headTok? with
         | some h => h == t
         | none   => false))

/-- Can this token **continue** an expression of entry `e`?

Exactly the leading token of an operator that *does* begin with a hole (`infx`, `infxl`,
`infxr`, `postfx`) — it arrives after the left operand, so `a + b` extends rather than stops.

`juxt` is deliberately absent: it has no token at all (`headTok? = none`) and continues via an
*operand*, which `startsOperand` already covers. -/
def continuesExpr (e : G.Ent) (t : Token G.isSep) : Bool :=
  (G.entry e).ops.any (fun o =>
    let op := (G.entry e).operator o
    op.startsWithHole &&
      (match op.headTok? with
       | some h => h == t
       | none   => false))

/-- **FOLLOW**: a token stops the parser iff it can neither start an operand nor continue one.

The tokens this *admits* are the ones that play neither role: interior and closing name tokens
(the `)` of `( _ )`, the `then` of `if _ then _`), which can only occur after a hole *inside* an
operator — and tokens the grammar does not know at all (a vernacular keyword, end of input). -/
def follow (e : G.Ent) : Token G.isSep → Bool :=
  fun t => !startsOperand e t && !continuesExpr e t

/-! ## The law

This is the one genuinely open obligation — the completeness half of the mixfix parser, which
has been open since the mixfix work began. Everything else in this file is free. -/

theorem mixfix_ok (e : G.Ent) (l : Level (G.entry e)) :
    RoundTrips (biparser G e l) (HeadIn (follow e)) := by
  sorry

/-- **The mixfix `IBip`** — a plug-in-ready biparser, modulo `mixfix_ok`. -/
def ibiparser (G : Grammar) (e : G.Ent) (l : Level (G.entry e)) :
    IBip (anyTok (G := G)) (follow e) (Expr G e l) (Expr G e l) where
  toCBiparser := biparser G e l
  firstOk := firstOk_any e l
  ok := mixfix_ok e l

end LambdaLab.CBiparser.Mixfix
