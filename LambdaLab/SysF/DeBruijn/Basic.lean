/-!
# System F, de Bruijn — syntax and the four substitutions

The second calculus, begun on the metatheory side per the architecture: the de Bruijn variant
is the reference, the named variant and its bridge come later, and the pipeline never sees
either until a `Language` instance exists. The layout mirrors `Stlc/DeBruijn/`.

Two binders now, so the counting doubles: terms bind term variables (`lam`) and type variables
(`tlam`); types bind type variables (`all`). Each variable kind is its own de Bruijn index
space, and the four substitution operations below are the complete inventory of crossings:

* `Ty.shift`/`Ty.subst` — type variables in types (`∀`-instantiation's engine);
* `Term.shift` — term variables in terms (`lam`-β's engine, as in STLC);
* `Term.tyShift` — *type* variables in terms: annotations and `tapp` arguments shift when a
  term crosses a `Λ`, which is why `Term.subst` invokes it in its `tlam` clause;
* `Term.tsubst` — a type for a type variable throughout a term (`Λ`-β's engine).

## Two decisions, both made for the embedding and the tower

**No `mvar`.** The STLC `Ty` carries an opaque metavariable constructor because its elaborator
solves first-order constraints; System F is the no-holes language — its inference is undecidable
and unprincipal, so elaboration will be checking, `sourceSupp := []` — and a type-level `mvar`
under `∀` would be a *scoped* metavariable, which the first-order `Subst Nat Ty` machinery
cannot express without capture. Leaving it out makes the tower's `MVars` layer trivial rather
than treacherous: substitution of metavariables that do not exist is the identity, and every
substitution law holds by `rfl`-adjacent proofs.

**Free type variables are legal, and atom-like.** The judgement (`Typing/Basic.lean`) does not
check type-variable scoping: a free `Ty.var n` types like an opaque base type — equal to itself,
no rules — exactly as STLC's `Ty.mvar n` does. That is not sloppiness but the embedding: STLC's
opaque atoms *become* F's type variables (`Ty.mvar n ↦ Ty.var n`, `Embed.lean`), which is what
will make STLC a subobject of System F in `DBSys` — the inclusion is structural, rule for rule.
-/

namespace LambdaLab.SysF.DeBruijn

/-- The types: a type variable (de Bruijn), the base type, arrows, and `∀`. -/
inductive Ty where
  | var   : Nat → Ty
  | base  : Ty
  | arrow : Ty → Ty → Ty
  | all   : Ty → Ty
  deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arrow

/-- Shift the type variables at or above the cutoff `c` — a type moving under one more `∀`. -/
def Ty.shift (c : Nat) : Ty → Ty
  | .var n     => if n < c then .var n else .var (n + 1)
  | .base      => .base
  | .arrow a b => .arrow (a.shift c) (b.shift c)
  | .all a     => .all (a.shift (c + 1))

/-- Substitute `σ` for type variable `n`, decrementing the variables above it — the binder it
came from is gone. The `all` clause shifts `σ`: it is moving under a `∀`. -/
def Ty.subst : Ty → Nat → Ty → Ty
  | .var m, n, σ =>
      if m = n then σ
      else if m > n then .var (m - 1)
      else .var m
  | .base, _, _ => .base
  | .arrow a b, n, σ => .arrow (a.subst n σ) (b.subst n σ)
  | .all a, n, σ => .all (a.subst (n + 1) (σ.shift 0))

/-- The terms: STLC's three constructors, plus type abstraction and type application. -/
inductive Term where
  | var  : Nat → Term
  | lam  : Ty → Term → Term
  | app  : Term → Term → Term
  | tlam : Term → Term
  | tapp : Term → Ty → Term
  deriving DecidableEq, Repr

/-- Shift the *term* variables at or above `c`. `tlam` binds no term variable, so its clause
does not bump the cutoff. -/
def Term.shift (c : Nat) : Term → Term
  | .var n     => if n < c then .var n else .var (n + 1)
  | .lam τ e   => .lam τ (e.shift (c + 1))
  | .app e₁ e₂ => .app (e₁.shift c) (e₂.shift c)
  | .tlam e    => .tlam (e.shift c)
  | .tapp e τ  => .tapp (e.shift c) τ

/-- Shift the *type* variables of a term — every annotation and every `tapp` argument — at or
above `c`. This is what a term undergoes when it crosses a `Λ`. -/
def Term.tyShift (c : Nat) : Term → Term
  | .var n     => .var n
  | .lam τ e   => .lam (τ.shift c) (e.tyShift c)
  | .app e₁ e₂ => .app (e₁.tyShift c) (e₂.tyShift c)
  | .tlam e    => .tlam (e.tyShift (c + 1))
  | .tapp e τ  => .tapp (e.tyShift c) (τ.shift c)

/-- Substitute `v` for term variable `n`. Crossing a `lam` shifts `v`'s *term* variables;
crossing a `tlam` shifts its *type* variables — the clause that has no STLC ancestor. -/
def Term.subst : Term → Nat → Term → Term
  | .var m, n, v =>
      if m = n then v
      else if m > n then .var (m - 1)
      else .var m
  | .lam τ e, n, v => .lam τ (e.subst (n + 1) (v.shift 0))
  | .app e₁ e₂, n, v => .app (e₁.subst n v) (e₂.subst n v)
  | .tlam e, n, v => .tlam (e.subst n (v.tyShift 0))
  | .tapp e τ, n, v => .tapp (e.subst n v) τ

/-- Substitute the type `σ` for type variable `n` throughout a term — `Λ`-β's engine. -/
def Term.tsubst : Term → Nat → Ty → Term
  | .var m, _, _ => .var m
  | .lam τ e, n, σ => .lam (τ.subst n σ) (e.tsubst n σ)
  | .app e₁ e₂, n, σ => .app (e₁.tsubst n σ) (e₂.tsubst n σ)
  | .tlam e, n, σ => .tlam (e.tsubst (n + 1) (σ.shift 0))
  | .tapp e τ, n, σ => .tapp (e.tsubst n σ) (τ.subst n σ)

end LambdaLab.SysF.DeBruijn

/-! ## Example terms -/

namespace LambdaLab.SysF.DeBruijn.Examples

open LambdaLab.SysF.DeBruijn

/-- `Λα. λx:α. x` — the polymorphic identity. -/
def polyId : Term := .tlam (.lam (.var 0) (.var 0))

/-- `∀α. α → α` — its type. -/
def polyIdTy : Ty := .all (.var 0 ⇒ .var 0)

/-- `(Λα. λx:α. x) [⋆]` — the identity, instantiated at the base type. -/
def idAtBase : Term := .tapp polyId .base

end LambdaLab.SysF.DeBruijn.Examples
