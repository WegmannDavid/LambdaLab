/-!
# The Calculus of Constructions, de Bruijn — one syntactic category

The third calculus, and the structural opposite of `SysF/`: where System F *doubled* the levels
— two binder kinds, two index spaces, four substitution operations, and a two-scope erasure the
bridge cannot yet express — CoC **collapses** them. Terms and types are one `Term`: sorts,
Π-types, abstractions, applications, variables, all in a single inductive with a single binder
discipline, a single de Bruijn index space, one `shift` and one `subst`. The de Bruijn tower
instantiates at `(Tm, Ty) := (Term, Term)`, a `Language` would need one parser where F wanted
two, and the bridge's single-alphabet erasure suffices again. Dependence does not add a level;
it removes one.

## The syntax

Pure CoC, PTS-style: two sorts `*` (`Srt.prop`) and `□` (`Srt.typ`), with `* : □` and `□`
untypeable; `pi A B` binds in `B`, `lam A b` binds in `b`. There is no separate arrow — `A ⇒ B`
is the non-dependent `pi A (B.shift 0)` — and no `mvar`, for the reasons `SysF/DeBruijn`'s
header gives, now with even more force: a metavariable in a dependent type is scoped over both
the typing context and every enclosing binder.

`shift` and `subst` are *structural* — no well-founded recursion, since there is no α-renaming
to route around — so both compute definitionally, and the examples at the bottom typecheck by
constructors and `rfl` alone.
-/

namespace LambdaLab.CoC.DeBruijn

/-- The two sorts: `*` (propositions/types of terms) and `□` (the sort of `*`). -/
inductive Srt where
  | prop
  | typ
  deriving DecidableEq, Repr

/-- One syntactic category: sorts, variables, `Π`, `λ`, application. -/
inductive Term where
  | sort : Srt → Term
  | var  : Nat → Term
  | pi   : Term → Term → Term
  | lam  : Term → Term → Term
  | app  : Term → Term → Term
  deriving DecidableEq, Repr

/-- Shift the variables at or above the cutoff `c` — one operation for the one index space. -/
def Term.shift (c : Nat) : Term → Term
  | .sort s  => .sort s
  | .var n   => if n < c then .var n else .var (n + 1)
  | .pi A B  => .pi (A.shift c) (B.shift (c + 1))
  | .lam A b => .lam (A.shift c) (b.shift (c + 1))
  | .app f a => .app (f.shift c) (a.shift c)

/-- Substitute `v` for variable `n`, decrementing above — one operation, structural, crossing
the one binder kind by shifting the value. -/
def Term.subst : Term → Nat → Term → Term
  | .sort s, _, _ => .sort s
  | .var m, n, v =>
      if m = n then v
      else if m > n then .var (m - 1)
      else .var m
  | .pi A B, n, v => .pi (A.subst n v) (B.subst (n + 1) (v.shift 0))
  | .lam A b, n, v => .lam (A.subst n v) (b.subst (n + 1) (v.shift 0))
  | .app f a, n, v => .app (f.subst n v) (a.subst n v)

/-- The non-dependent function space, as notation-of-convenience: `A ⇒ B` is `Π_:A. B` with `B`
not mentioning the binder. -/
def Term.arrow (A B : Term) : Term := .pi A (B.shift 0)

end LambdaLab.CoC.DeBruijn

/-! ## Example terms -/

namespace LambdaLab.CoC.DeBruijn.Examples

open LambdaLab.CoC.DeBruijn

/-- `λ(A:*). λ(x:A). x` — the polymorphic identity, now a single-`λ`-kind term. -/
def polyId : Term := .lam (.sort .prop) (.lam (.var 0) (.var 0))

/-- `Π(A:*). Π(x:A). A` — its type; System F's `∀` is just `Π` over `*`. -/
def polyIdTy : Term := .pi (.sort .prop) (.pi (.var 0) (.var 1))

end LambdaLab.CoC.DeBruijn.Examples
