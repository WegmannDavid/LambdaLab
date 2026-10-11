import LambdaLab.Nominal.Atom
import LambdaLab.Languages.CoC.DeBruijn.Syntax

/-!
# CoC, named — syntax and capture-avoiding substitution

The same calculus as `DeBruijn/Syntax.lean`, with names:

    s    ::= * | □
    t, A ::= x | s | Π x : A . B | λ x : A . t | t u

Names come from any `Atom N` — the development only decides their equality and draws fresh ones —
so a parser can use a name type whose values are already valid tokens.

## Substitution, simultaneous and capture-avoiding

`Tm.subst τ` replaces every free variable `x` by `τ x` at once. Crossing a binder extends the map
rather than renaming the body first, so the recursion is structural; a binder keeps its name
unless keeping it would capture something the substitution brings in, in which case it gets a
fresh one (`pick`). What it would capture is computed exactly: the free variables of the images of
the body's other free variables. There is one sort of variable — a type may mention a term
variable — so unlike System F there is one substitution, and every binder is like System F's type
binder: its name may occur in types.

Single substitution (`Tm.inst`, β) and renaming (`Tm.rename`) are instances. `Translation.lean`
proves the operation means what it should: it commutes with the translation to de Bruijn.
-/

namespace LambdaLab.Languages.CoC.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)
open LambdaLab.Languages.CoC.DeBruijn (Srt)

/-! ## Syntax -/

inductive Tm (N : Type) where
  | var : N → Tm N
  | sort : Srt → Tm N
  | pi : N → Tm N → Tm N → Tm N
  | lam : N → Tm N → Tm N → Tm N
  | app : Tm N → Tm N → Tm N
  deriving Repr

variable {N : Type} [Atom N]

/-! ## Free variables and size -/

/-- The free variables. -/
def Tm.fv : Tm N → List N
  | .var x => [x]
  | .sort _ => []
  | .pi x A B => A.fv ++ B.fv.filter (· ≠ x)
  | .lam x A t => A.fv ++ t.fv.filter (· ≠ x)
  | .app t u => t.fv ++ u.fv

/-- The size of the tree, every constructor counting one. -/
def Tm.size : Tm N → Nat
  | .var _ => 1
  | .sort _ => 1
  | .pi _ A B => A.size + B.size + 1
  | .lam _ A t => A.size + t.size + 1
  | .app t u => t.size + u.size + 1

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

/-- What a binder `x` over the body `B` must avoid under `τ`: the free variables of the images of
the body's other free variables. -/
def avoidFor (τ : N → Tm N) (x : N) (B : Tm N) : List N :=
  (B.fv.filter (· ≠ x)).flatMap (fun y => (τ y).fv)

/-- **Substitute for the free variables, all at once**, renaming a binder only when it would
capture. -/
def Tm.subst (τ : N → Tm N) : Tm N → Tm N
  | .var x => τ x
  | .sort s => .sort s
  | .pi x A B =>
      let z := pick x (avoidFor τ x B)
      .pi z (A.subst τ) (B.subst (upd τ x (.var z)))
  | .lam x A t =>
      let z := pick x (avoidFor τ x t)
      .lam z (A.subst τ) (t.subst (upd τ x (.var z)))
  | .app t u => .app (t.subst τ) (u.subst τ)

/-- `b[x := u]` — β. -/
def Tm.inst (b : Tm N) (x : N) (u : Tm N) : Tm N := b.subst (upd Tm.var x u)

/-- Rename the free variable `x` to `z`. -/
def Tm.rename (b : Tm N) (x z : N) : Tm N := b.inst x (.var z)

/-- Substituting variables for variables keeps the size. -/
theorem Tm.size_subst : ∀ (t : Tm N) (τ : N → Tm N), (∀ y, (τ y).size = 1) →
    (t.subst τ).size = t.size
  | .var x, _, h => by simp only [Tm.subst, Tm.size, h x]
  | .sort _, _, _ => rfl
  | .pi x A B, τ, h => by
      have h' : ∀ z y, (upd τ x (Tm.var z) y).size = 1 := fun z y => by
        unfold upd; split
        · rfl
        · exact h y
      simp only [Tm.subst, Tm.size, Tm.size_subst A τ h, Tm.size_subst B _ (h' _)]
  | .lam x A t, τ, h => by
      have h' : ∀ z y, (upd τ x (Tm.var z) y).size = 1 := fun z y => by
        unfold upd; split
        · rfl
        · exact h y
      simp only [Tm.subst, Tm.size, Tm.size_subst A τ h, Tm.size_subst t _ (h' _)]
  | .app t u, τ, h => by simp only [Tm.subst, Tm.size, Tm.size_subst t τ h, Tm.size_subst u τ h]

theorem Tm.size_rename (b : Tm N) (x z : N) : (b.rename x z).size = b.size :=
  Tm.size_subst b _ (fun y => by unfold upd; split <;> rfl)

end LambdaLab.Languages.CoC.Named
