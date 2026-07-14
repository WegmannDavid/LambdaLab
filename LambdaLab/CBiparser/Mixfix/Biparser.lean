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

/-! ## The per-level FOLLOW

`follow e` (the `Bool` in `Biparser.lean`) is the **loosest-level** instance and is what the
`IBip` index needs. The induction needs the level-indexed version, and only as a `Prop` —
it never has to be computed. -/

/-- A token can **continue** an expression at level `l` if some operator *valid at `l`* can
consume it as a continuation:

* a left-recursive operator whose leading token is `t` (it arrives after the left operand), or
* juxtaposition — which continues via an *operand*, so any operand-starter continues it.

The `Level.condition l o` guard is the whole point: at a tighter level, juxtaposition is not
applicable, so a variable **does not** continue — which is exactly why the operands of `f x y`
parse exactly, even though a variable is never in the loosest-level FOLLOW. -/
def ContinuesAt (e : G.Ent) (l : Level (G.entry e)) (t : Token G.isSep) : Prop :=
  (∃ o, Level.condition l o ∧ ((G.entry e).operator o).startsWithHole = true ∧
        ((G.entry e).operator o).headTok? = some t)
  ∨ (∃ j, Level.condition l j ∧ (G.entry e).operator j = Operator.juxt ∧
          startsOperand e t = true)

/-- **FOLLOW at a level**: the tokens that cannot extend an expression at `l`. -/
def FollowAt (e : G.Ent) (l : Level (G.entry e)) (rest : List (Token G.isSep)) : Prop :=
  ∀ t, rest.head? = some t → ¬ ContinuesAt e l t

/-- The computable `follow` is the **strongest** FOLLOW: it excludes *every* operator, not just
those valid at a level. So it implies `FollowAt` at every level -- which is what lets the
loosest-level `IBip` index feed the level-indexed induction. -/
theorem followAt_of_follow {e : G.Ent} {l : Level (G.entry e)} {rest : List (Token G.isSep)}
    (h : HeadIn (follow e) rest) : FollowAt e l rest := by
  intro t ht hcon
  have hf : follow e t = true := h t ht
  simp only [follow, Bool.and_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨hstart, hcont⟩ := hf
  rcases hcon with ⟨o, _, hhole, hhead⟩ | ⟨j, _, hjuxt, hstart'⟩
  · -- `t` heads a left-recursive operator, so `continuesExpr` should have been true
    have : continuesExpr e t = true := by
      simp only [continuesExpr, List.any_eq_true]
      exact ⟨o, (G.entry e).ops_complete o, by simp [hhole, hhead]⟩
    rw [this] at hcont; exact absurd hcont (by simp)
  · -- `t` starts an operand
    rw [hstart'] at hstart; exact absurd hstart (by simp)

/-! ## Interior seams land in the FOLLOW of the hole's entry

The one consequence of `interiorTerminates` that the round-trip law consumes: at every interior
seam of an operator — the `)` of `( _ )`, the `then` of `if _ then _` — the following token is in
the FOLLOW of **the entry that parses the hole**. That is what lets an operator's inner expression
be parsed *exactly*, and it is the crux of `parseExpr_exact`.

Note the entry: `follow e'`, not `follow e`. The hole may belong to a different entry than the
operator hosting it, and it is the *hole's* parser that has to stop. -/

theorem follow_of_holeFollower {e e' : G.Ent} {o : (G.entry e).Op} {t : Token G.isSep}
    (h : (e', t) ∈ ((G.entry e).operator o).holeFollowers) : follow e' t = true := by
  obtain ⟨hvar, hhead⟩ := G.interiorTerminates e o e' t h
  have key : ∀ o' : (G.entry e').Op, (match ((G.entry e').operator o').headTok? with
      | some h => h.val == t.val | none => false) = false := by
    intro o'
    cases hk : ((G.entry e').operator o').headTok? with
    | none => rfl
    | some h =>
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he; exact hhead o' (by rw [hk, Subtype.ext he])
  simp [follow, startsOperand, continuesExpr, hvar, key]

/-! ## The law

The round-trip law lives in `Complete.lean`, because it needs an **unambiguity** hypothesis on
the grammar — which is unavoidable for any *deterministic* parser: if two distinct trees flatten
alike, the parser returns one of them and the other cannot round-trip. `headsDistinct` does not
supply that.

`Complete.lean` also builds the plug-in-ready `IBip` from it. -/

end LambdaLab.CBiparser.Mixfix
