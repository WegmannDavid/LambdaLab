import LambdaLab.Stlc.Named.Syntax.Basic
import LambdaLab.Stlc.Named.Basic

/-!
# Truncation: concrete syntax tree → `Term`

`truncate` turns a parsed `Expr stlc .loosest` (the concrete syntax tree) into a
named-STLC `Term`. The correspondence:

* a variable leaf      → `Term.var`
* `paren` (grouping)   → its inner term (parentheses vanish — no `Term` node)
* `app`  (juxtaposition) → `Term.app`
* `lam`  (`\lambda x . body`) → `Term.lam`, reading the binder name out of the
  `varGrammar` sub-hole, with a **fresh `Ty.mvar` annotation**.

Surface `\lambda x . e` carries no type, but `Term.lam` needs one, and the
elaborator (`W`) *uses* a binder's annotation as its type — so each binder must
get a *distinct* metavariable, else two binders would be forced equal. We thread
a counter `n` to hand out `Ty.mvar n`, `Ty.mvar (n+1)`, …; the elaborator then
solves them. (The annotations are otherwise "don't cares".)
-/

namespace LambdaLab.Stlc.Named.Syntax

open LambdaLab.Parser.Mixfix

/-- The bound-variable name of a `varGrammar` parse — always a `var` leaf, since
`varGrammar` has no operators. -/
def binderName : Expr varGrammar .loosest → String
  | .var t _ => t
  | .op o _ _ => o.elim

/-- Truncate, threading a fresh-`mvar` counter `n` (one per lambda binder). -/
def truncateAux (n : Nat) {l : Level stlc} (e : Expr stlc l) : Term × Nat :=
  match e with
  | .var t _ => (Term.var t, n)
  | .op .paren _ (.namePart _ (.hole inner (.namePart _ .nil))) =>
      truncateAux n inner
  | .op .app _ (.hole f (.hole x .nil)) =>
      let (tf, n₁) := truncateAux n f
      let (tx, n₂) := truncateAux n₁ x
      (Term.app tf tx, n₂)
  | .op .lam _ (.namePart _ (.subHole _ bnd (.namePart _ (.hole body .nil)))) =>
      let (tbody, n₁) := truncateAux (n + 1) body
      (Term.lam (binderName bnd) (Ty.mvar n) tbody, n₁)

/-- Truncate a top-level concrete syntax tree to a `Term`. -/
def truncate (e : Expr stlc .loosest) : Term := (truncateAux 0 e).1

/-- String → `Term`: parse, then truncate the first parse (for demos). -/
def parseTruncate (s : String) : Option Term := (parse s).head?.map truncate

-- identity: `lam "x" ?0 (var "x")`
#eval parseTruncate "\\lambda x . x"
-- left-assoc application: `app (app f x) y`
#eval parseTruncate "f x y"
-- applied identity: `app (lam "x" ?0 (var "x")) (var "y")`
#eval parseTruncate "( \\lambda x . x ) y"
-- nested lambda — distinct binder mvars ?0, ?1:
--   `lam "f" ?0 (lam "x" ?1 (app (var "f") (var "x")))`
#eval parseTruncate "\\lambda f . ( \\lambda x . f x )"

end LambdaLab.Stlc.Named.Syntax
