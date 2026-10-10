import LambdaLab.Nominal.Atom

/-!
# System F, named — syntax and capture-avoiding substitution

The same calculus as `DeBruijn/Syntax.lean`, with names:

    A, B ::= α | A → B | ∀ α . A
    t, u ::= x | λ x : A . t | t u | Λ α . t | t [A]

Names are drawn from any `Atom N` — the development only decides equality of names and draws
fresh ones — so a parser can use a name type whose values are already valid tokens.

## Substitution, simultaneous and capture-avoiding

One operation does all the work: `Tm.subst σ τ` replaces every free type variable `α` by `σ α`
and every free term variable `x` by `τ x`, at once. Crossing a binder extends the maps rather than
renaming the body first, so the recursion is structural; and a binder keeps its name unless
keeping it would capture something the substitution brings in, in which case it gets a fresh one
(`pick`). What it would capture is computed exactly: the free variables of the images of the
binder's own free variables.

* crossing `λ x`, the new name must avoid the free *term* variables of the substituted terms;
* crossing `Λ α`, it must avoid the free *type* variables of the substituted types **and** of the
  substituted terms — a term brought under a `Λ` carries its type variables with it.

Every single substitution is an instance: `Tm.inst` (β), `Tm.tinst` (type-β), `Ty.inst`, and the
type-variable renaming `Tm.trename`.

`Translation.lean` proves the operation means what it should: it commutes with the translation
to de Bruijn.
-/

namespace LambdaLab.Languages.SystemF.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)

/-! ## Syntax -/

inductive Ty (N : Type) where
  | var : N → Ty N
  | arr : Ty N → Ty N → Ty N
  | all : N → Ty N → Ty N
  deriving Repr

inductive Tm (N : Type) where
  | var : N → Tm N
  | lam : N → Ty N → Tm N → Tm N
  | app : Tm N → Tm N → Tm N
  | tlam : N → Tm N → Tm N
  | tapp : Tm N → Ty N → Tm N
  deriving Repr

variable {N : Type} [Atom N]

/-! ## Free variables -/

/-- The free type variables of a type. -/
def Ty.ftv : Ty N → List N
  | .var α => [α]
  | .arr A B => A.ftv ++ B.ftv
  | .all α A => A.ftv.filter (· ≠ α)

/-- The free term variables of a term. -/
def Tm.fv : Tm N → List N
  | .var x => [x]
  | .lam x _ b => b.fv.filter (· ≠ x)
  | .app t u => t.fv ++ u.fv
  | .tlam _ b => b.fv
  | .tapp t _ => t.fv

/-- The free type variables of a term: those of its annotations and type arguments, minus the ones
a `Λ` binds. -/
def Tm.ftv : Tm N → List N
  | .var _ => []
  | .lam _ A b => A.ftv ++ b.ftv
  | .app t u => t.ftv ++ u.ftv
  | .tlam α b => b.ftv.filter (· ≠ α)
  | .tapp t B => t.ftv ++ B.ftv

/-- The size of a term's tree, annotations not counted. -/
def Tm.size : Tm N → Nat
  | .var _ => 1
  | .lam _ _ b => b.size + 1
  | .app t u => t.size + u.size + 1
  | .tlam _ b => b.size + 1
  | .tapp t _ => t.size + 1

/-! ## Substitution -/

/-- A map updated at one name. -/
def upd {X : Type} (f : N → X) (a : N) (v : X) : N → X := fun b => if b = a then v else f b

@[simp] theorem upd_same {X : Type} (f : N → X) (a : N) (v : X) : upd f a v a = v := by
  simp [upd]

theorem upd_ne {X : Type} (f : N → X) {a b : N} (v : X) (h : b ≠ a) : upd f a v b = f b := by
  simp [upd, h]

/-- Keep the name `a` if it is outside `avoid`; otherwise draw a fresh one. -/
def pick (a : N) (avoid : List N) : N := if a ∈ avoid then freshFor avoid else a

theorem pick_not_mem (a : N) (avoid : List N) : pick a avoid ∉ avoid := by
  unfold pick
  split
  · exact freshFor_not_in _
  · assumption

/-- **Substitute for the free type variables of a type**, renaming a `∀` binder only when it would
capture. -/
def Ty.subst (σ : N → Ty N) : Ty N → Ty N
  | .var α => σ α
  | .arr A B => .arr (A.subst σ) (B.subst σ)
  | .all α A =>
      let β := pick α ((A.ftv.filter (· ≠ α)).flatMap (fun γ => (σ γ).ftv))
      .all β (A.subst (upd σ α (.var β)))

/-- **Substitute for the free type and term variables of a term at once**, renaming a binder only
when it would capture. -/
def Tm.subst (σ : N → Ty N) (τ : N → Tm N) : Tm N → Tm N
  | .var x => τ x
  | .lam x A b =>
      let z := pick x ((b.fv.filter (· ≠ x)).flatMap (fun y => (τ y).fv))
      .lam z (A.subst σ) (b.subst σ (upd τ x (.var z)))
  | .app t u => .app (t.subst σ τ) (u.subst σ τ)
  | .tlam α b =>
      let β := pick α ((b.ftv.filter (· ≠ α)).flatMap (fun γ => (σ γ).ftv) ++
        b.fv.flatMap (fun y => (τ y).ftv))
      .tlam β (b.subst (upd σ α (.var β)) τ)
  | .tapp t B => .tapp (t.subst σ τ) (B.subst σ)

/-- `A[α := B]`. -/
def Ty.inst (A : Ty N) (α : N) (B : Ty N) : Ty N := A.subst (upd Ty.var α B)

/-- `b[x := u]` — β. -/
def Tm.inst (b : Tm N) (x : N) (u : Tm N) : Tm N := b.subst Ty.var (upd Tm.var x u)

/-- `b[α := B]` — type-β. -/
def Tm.tinst (b : Tm N) (α : N) (B : Ty N) : Tm N := b.subst (upd Ty.var α B) Tm.var

/-- Rename the free type variable `α` to `β`. -/
def Tm.trename (b : Tm N) (α β : N) : Tm N := b.tinst α (.var β)

/-- Substituting variables for term variables keeps the size. -/
theorem Tm.size_subst : ∀ (t : Tm N) (σ : N → Ty N) (τ : N → Tm N), (∀ y, (τ y).size = 1) →
    (t.subst σ τ).size = t.size
  | .var x, _, _, h => by simp only [Tm.subst, Tm.size, h x]
  | .lam x A b, σ, τ, h => by
      simp only [Tm.subst, Tm.size]
      rw [Tm.size_subst b σ _ (fun y => by
        unfold upd
        split
        · rfl
        · exact h y)]
  | .app t u, σ, τ, h => by simp only [Tm.subst, Tm.size, Tm.size_subst t σ τ h, Tm.size_subst u σ τ h]
  | .tlam α b, σ, τ, h => by simp only [Tm.subst, Tm.size, Tm.size_subst b _ τ h]
  | .tapp t B, σ, τ, h => by simp only [Tm.subst, Tm.size, Tm.size_subst t σ τ h]

theorem Tm.size_trename (b : Tm N) (α β : N) : (b.trename α β).size = b.size :=
  Tm.size_subst b _ _ (fun _ => rfl)

end LambdaLab.Languages.SystemF.Named
