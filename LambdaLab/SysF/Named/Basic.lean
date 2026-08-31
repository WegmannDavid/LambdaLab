import LambdaLab.Nominal.Atom

/-!
# System F, named-variable presentation

The named mirror of `SysF/DeBruijn/Basic.lean`, built on `Stlc/Named/Basic.lean`'s idioms —
capture-avoiding substitution by `Atom.freshFor`, termination by size through the renaming
lemmas — now doubled: there are **two name spaces**, term names `N` and type names `TN`, each
its own `Atom`. Two parameters rather than one shared alphabet, mirroring the de Bruijn side's
two index spaces; the tower only ever sees `N` (contexts are keyed by term names; type names
are internal to `Ty`), so `Term N TN` and `Ty TN` instantiate `TypeSystem.Named.*` at `N` with
`TN` riding along as an ordinary parameter.

The inventory of crossings, named edition:

* `Ty.subst` — capture-avoiding type-for-type-variable in a type (`∀`-instantiation);
* `Term.subst` — term-for-term-variable, avoiding capture **twice over**: a `lam` binder is
  renamed when it would capture a free *term* variable of the value (as in STLC), and a `tlam`
  binder when it would capture a free *type* variable of the value's annotations — the clause
  with no STLC ancestor, and the named counterpart of the de Bruijn `Term.tyShift` call;
* `Term.tsubst` — type-for-type-variable throughout a term (`Λ`-β), renaming shadow-free
  `tlam` binders that would capture the substituted type's variables.

No `mvar`, as on the de Bruijn side and for its reasons (see that header). The awkward
STLC-`mvar`-as-type-variable question lives entirely in the embedding and is deliberately not
reproduced here.
-/

namespace LambdaLab.SysF.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)

variable {N TN : Type} [Atom N] [Atom TN]

/-! ## Types -/

/-- Types: a type variable, the base type, arrows, and `∀ a. τ`. -/
inductive Ty (TN : Type) where
  | tvar  : TN → Ty TN
  | base  : Ty TN
  | arrow : Ty TN → Ty TN → Ty TN
  | all   : TN → Ty TN → Ty TN
  deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arrow

def Ty.freeVars : Ty TN → List TN
  | .tvar a    => [a]
  | .base      => []
  | .arrow a b => a.freeVars ++ b.freeVars
  | .all a τ   => τ.freeVars.filter (· ≠ a)

/-- All type variables, free and bound — freshness must clear binders too. -/
def Ty.allVars : Ty TN → List TN
  | .tvar a    => [a]
  | .base      => []
  | .arrow a b => a.allVars ++ b.allVars
  | .all a τ   => a :: τ.allVars

def Ty.size : Ty TN → Nat
  | .tvar _    => 1
  | .base      => 1
  | .arrow a b => 1 + a.size + b.size
  | .all _ τ   => 1 + τ.size

/-- Type-variable renaming: structural, stopping at a shadowing `∀`. -/
def Ty.rename : Ty TN → TN → TN → Ty TN
  | .tvar a,    b, c => if a = b then .tvar c else .tvar a
  | .base,      _, _ => .base
  | .arrow t u, b, c => .arrow (t.rename b c) (u.rename b c)
  | .all a τ,   b, c =>
      if a = b then .all a τ
      else .all a (τ.rename b c)

theorem Ty.rename_size (τ : Ty TN) (b c : TN) : (τ.rename b c).size = τ.size := by
  induction τ with
  | tvar a => simp only [Ty.rename]; split <;> rfl
  | base => rfl
  | arrow t u iht ihu => simp only [Ty.rename, Ty.size, iht, ihu]
  | all a τ ih => simp only [Ty.rename]; split <;> simp [Ty.size, ih]

/-- Capture-avoiding type-for-type-variable substitution, `Stlc`'s `Term.subst` one level up:
a `∀`-binder that would capture a free variable of `σ` is α-renamed fresh first. -/
def Ty.subst (τ : Ty TN) (a : TN) (σ : Ty TN) : Ty TN :=
  match τ with
  | .tvar b => if a = b then σ else .tvar b
  | .base => .base
  | .arrow t u => .arrow (t.subst a σ) (u.subst a σ)
  | .all b body =>
      if a = b then .all b body
      else if b ∈ σ.freeVars then
        let c := freshFor (σ.freeVars ++ body.allVars ++ [a])
        .all c ((body.rename b c).subst a σ)
      else .all b (body.subst a σ)
  termination_by τ.size
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Ty.size, Ty.rename_size]
    all_goals omega

/-! ## Terms -/

/-- Terms: STLC's three constructors over two alphabets, plus `Λ a. e` and `e [τ]`. -/
inductive Term (N TN : Type) where
  | var  : N → Term N TN
  | lam  : N → Ty TN → Term N TN → Term N TN
  | app  : Term N TN → Term N TN → Term N TN
  | tlam : TN → Term N TN → Term N TN
  | tapp : Term N TN → Ty TN → Term N TN
  deriving Repr

/-- Free *term* variables. `tlam` and `tapp` are transparent — they bind and mention only type
names. -/
def Term.freeVars : Term N TN → List N
  | .var x        => [x]
  | .lam y _ body => body.freeVars.filter (· ≠ y)
  | .app e₁ e₂    => e₁.freeVars ++ e₂.freeVars
  | .tlam _ body  => body.freeVars
  | .tapp e _     => e.freeVars

/-- Free *type* variables: annotations and `tapp` arguments contribute, `tlam` binds. -/
def Term.tyFreeVars : Term N TN → List TN
  | .var _        => []
  | .lam _ τ body => τ.freeVars ++ body.tyFreeVars
  | .app e₁ e₂    => e₁.tyFreeVars ++ e₂.tyFreeVars
  | .tlam a body  => body.tyFreeVars.filter (· ≠ a)
  | .tapp e τ     => e.tyFreeVars ++ τ.freeVars

/-- All term variables, binders included. -/
def Term.allVars : Term N TN → List N
  | .var x        => [x]
  | .lam y _ body => y :: body.allVars
  | .app e₁ e₂    => e₁.allVars ++ e₂.allVars
  | .tlam _ body  => body.allVars
  | .tapp e _     => e.allVars

/-- All type variables, binders and annotations included. -/
def Term.tyAllVars : Term N TN → List TN
  | .var _        => []
  | .lam _ τ body => τ.allVars ++ body.tyAllVars
  | .app e₁ e₂    => e₁.tyAllVars ++ e₂.tyAllVars
  | .tlam a body  => a :: body.tyAllVars
  | .tapp e τ     => e.tyAllVars ++ τ.allVars

def Term.size : Term N TN → Nat
  | .var _        => 1
  | .lam _ _ body => 1 + body.size
  | .app e₁ e₂    => 1 + e₁.size + e₂.size
  | .tlam _ body  => 1 + body.size
  | .tapp e _     => 1 + e.size

/-- Term-variable renaming, stopping at a shadowing `lam`. -/
def Term.rename : Term N TN → N → N → Term N TN
  | .var x,        y, z => if x = y then .var z else .var x
  | .lam x τ body, y, z =>
      if x = y then .lam x τ body
      else .lam x τ (body.rename y z)
  | .app e₁ e₂,    y, z => .app (e₁.rename y z) (e₂.rename y z)
  | .tlam a body,  y, z => .tlam a (body.rename y z)
  | .tapp e τ,     y, z => .tapp (e.rename y z) τ

/-- Type-variable renaming throughout a term, stopping at a shadowing `tlam`; annotations
rename by `Ty.rename`. -/
def Term.tyRename : Term N TN → TN → TN → Term N TN
  | .var x,        _, _ => .var x
  | .lam x τ body, b, c => .lam x (τ.rename b c) (body.tyRename b c)
  | .app e₁ e₂,    b, c => .app (e₁.tyRename b c) (e₂.tyRename b c)
  | .tlam a body,  b, c =>
      if a = b then .tlam a body
      else .tlam a (body.tyRename b c)
  | .tapp e τ,     b, c => .tapp (e.tyRename b c) (τ.rename b c)

omit [Atom TN] in
theorem Term.rename_size (e : Term N TN) (y z : N) : (e.rename y z).size = e.size := by
  induction e with
  | var x => simp only [Term.rename]; split <;> rfl
  | lam x τ body ih => simp only [Term.rename]; split <;> simp [Term.size, ih]
  | app e₁ e₂ ih₁ ih₂ => simp only [Term.rename, Term.size, ih₁, ih₂]
  | tlam a body ih => simp only [Term.rename, Term.size, ih]
  | tapp e τ ih => simp only [Term.rename, Term.size, ih]

omit [Atom N] in
theorem Term.tyRename_size (e : Term N TN) (b c : TN) : (e.tyRename b c).size = e.size := by
  induction e with
  | var x => rfl
  | lam x τ body ih => simp only [Term.tyRename, Term.size, ih]
  | app e₁ e₂ ih₁ ih₂ => simp only [Term.tyRename, Term.size, ih₁, ih₂]
  | tlam a body ih => simp only [Term.tyRename]; split <;> simp [Term.size, ih]
  | tapp e τ ih => simp only [Term.tyRename, Term.size, ih]

/-! ## Capture-avoiding substitution, twice over -/

/-- `e.subst x v`: replace the free *term* variable `x` by `v`. Capture is avoided in **both**
alphabets: a `lam` binder free in `v`'s term variables is renamed (as in STLC), and a `tlam`
binder free in `v`'s *type* variables is renamed too — carrying `v` under a `Λ` must not
capture the type variables of its annotations. The named counterpart of the de Bruijn
`Term.subst`'s `tyShift` clause. -/
def Term.subst (e : Term N TN) (x : N) (v : Term N TN) : Term N TN :=
  match e with
  | .var y => if x = y then v else .var y
  | .lam y τ body =>
      if x = y then .lam y τ body
      else if y ∈ v.freeVars then
        let z := freshFor (v.freeVars ++ body.allVars ++ [x])
        .lam z τ ((body.rename y z).subst x v)
      else .lam y τ (body.subst x v)
  | .app e₁ e₂ => .app (e₁.subst x v) (e₂.subst x v)
  | .tlam a body =>
      if a ∈ v.tyFreeVars then
        let c := freshFor (v.tyFreeVars ++ body.tyAllVars)
        .tlam c ((body.tyRename a c).subst x v)
      else .tlam a (body.subst x v)
  | .tapp e τ => .tapp (e.subst x v) τ
  termination_by e.size
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Term.size]
    all_goals first
      | omega
      | (rw [Term.rename_size]; omega)
      | (rw [Term.tyRename_size]; omega)

/-- `e.tsubst a σ`: replace the free *type* variable `a` by `σ` throughout — annotations and
`tapp` arguments via `Ty.subst`, shadow-free `tlam` binders renamed when they would capture a
variable of `σ`. `Λ`-β's engine. -/
def Term.tsubst (e : Term N TN) (a : TN) (σ : Ty TN) : Term N TN :=
  match e with
  | .var y => .var y
  | .lam y τ body => .lam y (τ.subst a σ) (body.tsubst a σ)
  | .app e₁ e₂ => .app (e₁.tsubst a σ) (e₂.tsubst a σ)
  | .tlam b body =>
      if a = b then .tlam b body
      else if b ∈ σ.freeVars then
        let c := freshFor (σ.freeVars ++ body.tyAllVars ++ [a])
        .tlam c ((body.tyRename b c).tsubst a σ)
      else .tlam b (body.tsubst a σ)
  | .tapp e τ => .tapp (e.tsubst a σ) (τ.subst a σ)
  termination_by e.size
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Term.size]
    all_goals first
      | omega
      | (rw [Term.tyRename_size]; omega)

end LambdaLab.SysF.Named

/-! ## Example terms -/

namespace LambdaLab.SysF.Named.Examples

open LambdaLab.SysF.Named

/-- `Λa. λx:a. x` — the polymorphic identity. -/
def polyId : Term String String := .tlam "a" (.lam "x" (.tvar "a") (.var "x"))

/-- `∀a. a → a` — its type. -/
def polyIdTy : Ty String := .all "a" (.tvar "a" ⇒ .tvar "a")

/-- `(Λa. λx:a. x) [⋆]`. -/
def idAtBase : Term String String := .tapp polyId .base

end LambdaLab.SysF.Named.Examples
