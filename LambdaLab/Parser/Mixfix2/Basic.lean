import LambdaLab.Parser.Basic


namespace LambdaLab.Parser.Mixfix2

inductive Associativity where
  | left
  | right
  | nonAssoc
deriving DecidableEq, Repr

inductive Fixity where
  | closed
  | prefix
  | postfix
  | infix (assoc : Associativity)
deriving DecidableEq, Repr

/-- Number of recursive holes an operator has, as a function of its
fixity and its number of name-parts. The four fixities differ only in
whether the token shape starts and/or ends with a hole:

* `closed`  : `n₀ _ n₁ _ … _ nₖ`   — holes between parts      → `n - 1`
* `prefix`  : `n₀ _ … nₖ _`         — trailing hole           → `n`
* `postfix` : `_ n₀ _ … _ nₖ`       — leading hole            → `n`
* `infix`   : `_ n₀ _ … _ nₖ _`     — leading and trailing    → `n + 1`
-/
def Fixity.arity : Fixity → Nat → Nat
  | .closed,  n => n - 1
  | .prefix,  n => n
  | .postfix, n => n
  | .infix _, n => n + 1

/-- A mixfix operator: a fixity together with its non-empty list of
name-parts. The recursive holes are not stored — they are determined by
`fixity` and `nameParts.length`. There is no carrier type and no `build`
function: an operator describes *shape* only. -/
structure Operator where
  fixity : Fixity
  nameParts : List String
  nameParts_ne_nil : nameParts ≠ []

/-- The number of recursive holes of an operator. -/
def Operator.arity (op : Operator) : Nat :=
  op.fixity.arity op.nameParts.length

/-- A nullary constant: a `closed` operator with a single name-part and
therefore zero holes (e.g. `zero`, `true`). Constants are not a separate
kind of grammar entry — they are exactly this degenerate operator. -/
def Operator.const (s : String) : Operator where
  fixity := .closed
  nameParts := [s]
  nameParts_ne_nil := by simp

@[simp] theorem Operator.const_arity (s : String) : (Operator.const s).arity = 0 := rfl

/-- All name-part tokens of an operator array, concatenated in order. -/
def nameTokens (ops : Array Operator) : List String :=
  ops.toList.flatMap (·.nameParts)

/-- A grammar: operators in loosest-first precedence order, with every
name-part token distinct across the whole grammar. This "unique reading"
condition is what makes `parse` a left inverse of `flatten` — each token
identifies exactly one operator-and-position, so parsing is forced. -/
structure Grammar where
  ops : Array Operator
  nameParts_nodup : (nameTokens ops).Nodup

end LambdaLab.Parser.Mixfix2
