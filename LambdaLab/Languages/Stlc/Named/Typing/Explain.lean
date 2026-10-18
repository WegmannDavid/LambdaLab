import LambdaLab.Languages.Stlc.Named.Typing.JComplete

/-!
# STLC — why a declaration does not elaborate

For diagnostics only, and informal like every diagnostic: nothing here is proved, and nothing
proved depends on it. It is consulted after the elaborator (`elabMGU`) has said that no
substitution types a declaration, and says why, by retracing the elaborator's own two phases:

* **constraint generation** fails only at a variable that is not bound (`Term.unbound?`);
* otherwise **unification** fails, and the constraints are fed to `unify` one at a time — the body's
  own constraints first, innermost application first, then the one equating the body's type with
  the declared type. The first that cannot be added is the reason, read with everything solved
  before it applied: a function applied to an argument of the wrong type, something applied that
  is not a function, a type that would have to contain itself, or a body whose type is not the
  declared one.

Each constraint of the body comes from an application, and is tagged with it (`genTagged`, which
generates what `gen` generates), so the reason names the application at fault.
-/

namespace LambdaLab.Languages.Stlc.Named

open LambdaLab.Nominal (Atom)

variable {N : Type} [Atom N]

/-! ## Printing, as the surface writes it -/

/-- A type, as written: `⋆`, `_`, `?k`, `A → B`, arrows to the right. The anonymous `_` is the
metavariable `0`, and `?k` the metavariable `k + 1` (`Pipeline.lean`). -/
def Ty.render : Ty → String
  | .base => "⋆"
  | .mvar 0 => "_"
  | .mvar (k + 1) => s!"?{k}"
  | .arrow l@(.arrow _ _) c => s!"({l.render}) → {c.render}"
  | .arrow a c => s!"{a.render} → {c.render}"

/-- A term, as written, at a position: `0` anywhere, `1` a function being applied, `2` an
argument. -/
def Term.renderAt (showName : N → String) : Nat → Term N → String
  | _, .var x => showName x
  | p, .lam x α b =>
      let s := s!"λ {showName x} : {α.render} . {b.renderAt showName 0}"
      if p > 0 then s!"({s})" else s
  | p, .app f a =>
      let s := s!"{f.renderAt showName 1} {a.renderAt showName 2}"
      if p > 1 then s!"({s})" else s

/-- A term, as written. -/
def Term.render (showName : N → String) (t : Term N) : String := t.renderAt showName 0

/-! ## Retracing the elaborator -/

/-- The first variable of `t` that `Γ` and the binders around it do not bind. -/
def Term.unbound? : Ctx N → Term N → Option N
  | Γ, .var x => if (Γ.get? x).isSome then none else some x
  | Γ, .lam x α b => b.unbound? (Γ.cons x α)
  | Γ, .app f a => (f.unbound? Γ).or (a.unbound? Γ)

/-- **`gen`, with each constraint tagged by the application it comes from**: a subterm's
constraints before its application's own, so the innermost come first. -/
def genTagged : Ctx N → Term N → Nat → Option (Ty × List (Ty × Ty × Term N) × Nat)
  | Γ, .var x, n => (Γ.get? x).map fun τ => (τ, [], n)
  | Γ, .lam x α body, n =>
      match genTagged (Γ.cons x α) body n with
      | none => none
      | some (τb, C, n') => some (α ⇒ τb, C, n')
  | Γ, .app e₁ e₂, n =>
      match genTagged Γ e₁ n with
      | none => none
      | some (τ₁, C₁, n₁) =>
          match genTagged Γ e₂ n₁ with
          | none => none
          | some (τ₂, C₂, n₂) =>
              some (Ty.mvar n₂, C₁ ++ C₂ ++ [(τ₁, τ₂ ⇒ Ty.mvar n₂, .app e₁ e₂)], n₂ + 1)

/-- Does the metavariable `m` occur in the type? -/
def Ty.mentions (m : Nat) : Ty → Bool
  | .base => false
  | .mvar k => k == m
  | .arrow a b => a.mentions m || b.mentions m

/-- The first equation that cannot be added to the ones before it, with the most general solution
of those before it. -/
def firstUnsolvable (eqs : List (Ty × Ty)) : Option (Nat × Subst Nat Ty) :=
  ((List.range eqs.length).find? fun k => (unify (eqs.take (k + 1))).isNone).map fun k =>
    (k, (unify (eqs.take k)).getD ∅)

/-- Why an application is ill-typed: its function's type `f` cannot be matched with an argument's
type `a` and some result. -/
def appReason (showName : N → String) (e : Term N) (f a : Ty) : String :=
  match e with
  | .app e₁ e₂ =>
      let at_ := s!"in `{e.render showName}`: "
      match f with
      | .arrow d _ =>
          at_ ++ s!"`{e₁.render showName}` expects an argument of type {d.render}, but \
            `{e₂.render showName}` has type {a.render}"
      | .base => at_ ++ s!"`{e₁.render showName}` has type ⋆, so it cannot be applied"
      | .mvar m =>
          at_ ++ s!"`{e₁.render showName}` would need a type {(Ty.mvar m).render} = \
            {a.render} → … that contains itself"
  | _ => "a constraint of this declaration cannot be solved"

/-- Why the body's type `b` cannot be the declared type `d`. -/
def declReason (b d : Ty) : String :=
  let infinite := match b, d with
    | _, .mvar m => b.mentions m && b != d
    | .mvar m, _ => d.mentions m && b != d
    | _, _ => false
  if infinite then
    s!"the body has type {b.render}, which would have to equal the declared {d.render} — a type \
      containing itself"
  else s!"the body has type {b.render}, but the declaration says {d.render}"

/-- **Why `t` does not have type `τ` in `Γ`.** -/
def explainElab (showName : N → String) (Γ : Ctx N) (t : Term N) (τ : Ty) : String :=
  match genTagged Γ t (srcCounter Γ t τ) with
  | none =>
      match t.unbound? Γ with
      | some x => s!"`{showName x}` is not bound: it is neither a λ-bound variable nor an earlier \
          declaration"
      | none => "this declaration does not have its declared type"
  | some (τt, C, _) =>
      let eqs := C.map fun c => (c.1, c.2.1)
      match firstUnsolvable eqs with
      | some (k, σ) =>
          match C[k]? with
          | some (a, b, e) =>
              appReason showName e (HasSubst.pSubst a σ)
                (match HasSubst.pSubst b σ with | .arrow d _ => d | b' => b')
          | none => "this declaration does not have its declared type"
      | none =>
          match unify eqs with
          | some σ => declReason (HasSubst.pSubst τt σ) (HasSubst.pSubst τ σ)
          | none => "this declaration does not have its declared type"

/-- The metavariables of a type, in order of appearance. -/
def Ty.mvars : Ty → List Nat
  | .base => []
  | .mvar k => [k]
  | .arrow a b => a.mvars ++ b.mvars

/-- The metavariables of a term's annotations. -/
def Term.mvars : Term N → List Nat
  | .var _ => []
  | .lam _ α b => α.mvars ++ b.mvars
  | .app f a => f.mvars ++ a.mvars

/-- **What elaboration left undetermined**, in a declaration it otherwise typed. -/
def explainUnsolvedElab (showName : N → String) (t : Term N) (τ : Ty) : String :=
  let ms := (τ.mvars ++ t.mvars).eraseDups
  let names := ", ".intercalate (ms.map fun m => (Ty.mvar m).render)
  let where_ := if τ.mvars.isEmpty then s!"in the body `{t.render showName}`"
    else s!"in the type {τ.render}"
  s!"{names} {if ms.length = 1 then "is" else "are"} not determined by this declaration \
    ({where_}): nothing constrains {if ms.length = 1 then "it" else "them"}"

end LambdaLab.Languages.Stlc.Named
