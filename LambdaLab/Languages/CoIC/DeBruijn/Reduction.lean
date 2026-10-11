import LambdaLab.Languages.CoIC.DeBruijn.Syntax
import LambdaLab.Relation.Closure
import LambdaLab.Relation.Normalization

/-!
# CoC — reduction

Full β-reduction: a redex may be contracted anywhere, under binders and inside the domains of `Π`
and the annotations of `λ` alike — in CoC those are terms like any other, and a type may well
compute (`(λ X : * . X → X) A` is a type). `Red` is its reflexive-transitive closure.

Both are closed under renaming and substitution (`Step.subst`, `Red.subst`), and a reduction of
the substituted terms lifts through a substitution (`Red.subst_red`) — the two facts every
statement about conversion below is built from.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

open LambdaLab (RTC SN)

/-- **One step of β-reduction**, anywhere in the term. -/
inductive Step : Tm → Tm → Prop where
  | beta {A t u : Tm} : Step (.app (.lam A t) u) (t.inst u)
  | appL {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} : Step u u' → Step (.app t u) (.app t u')
  | lamA {A A' t : Tm} : Step A A' → Step (.lam A t) (.lam A' t)
  | lamB {A t t' : Tm} : Step t t' → Step (.lam A t) (.lam A t')
  | piA {A A' B : Tm} : Step A A' → Step (.pi A B) (.pi A' B)
  | piB {A B B' : Tm} : Step B B' → Step (.pi A B) (.pi A B')

/-- Many steps. -/
abbrev Red : Tm → Tm → Prop := RTC Step

theorem Step.var_inv {n : Nat} {t : Tm} : ¬ Step (.var n) t := nofun

theorem Step.sort_inv {s : Srt} {t : Tm} : ¬ Step (.sort s) t := nofun

/-! ## Renaming and substitution -/

theorem Step.ren {t t' : Tm} (h : Step t t') : ∀ ξ : Nat → Nat, Step (t.ren ξ) (t'.ren ξ) := by
  induction h with
  | @beta A t u =>
      intro ξ
      rw [Tm.ren_inst]
      exact .beta
  | appL _ ih => intro ξ; exact .appL (ih ξ)
  | appR _ ih => intro ξ; exact .appR (ih ξ)
  | lamA _ ih => intro ξ; exact .lamA (ih ξ)
  | lamB _ ih => intro ξ; exact .lamB (ih _)
  | piA _ ih => intro ξ; exact .piA (ih ξ)
  | piB _ ih => intro ξ; exact .piB (ih _)

theorem Step.subst {t t' : Tm} (h : Step t t') : ∀ σ : Nat → Tm, Step (t.subst σ) (t'.subst σ) := by
  induction h with
  | @beta A t u =>
      intro σ
      rw [Tm.subst_inst]
      exact .beta
  | appL _ ih => intro σ; exact .appL (ih σ)
  | appR _ ih => intro σ; exact .appR (ih σ)
  | lamA _ ih => intro σ; exact .lamA (ih σ)
  | lamB _ ih => intro σ; exact .lamB (ih _)
  | piA _ ih => intro σ; exact .piA (ih σ)
  | piB _ ih => intro σ; exact .piB (ih _)

/-! ## `Red` -/

/-- `Red` is a congruence for any operation that `Step` is. -/
theorem Red.map (f : Tm → Tm) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {a b : Tm}
    (h : Red a b) : Red (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hf hs)

theorem Red.app {t t' u u' : Tm} (ht : Red t t') (hu : Red u u') : Red (.app t u) (.app t' u') :=
  (Red.map (fun x => .app x u) .appL ht).trans (Red.map (fun x => .app t' x) .appR hu)

theorem Red.lam {A A' t t' : Tm} (hA : Red A A') (ht : Red t t') : Red (.lam A t) (.lam A' t') :=
  (Red.map (fun x => .lam x t) .lamA hA).trans (Red.map (fun x => .lam A' x) .lamB ht)

theorem Red.pi {A A' B B' : Tm} (hA : Red A A') (hB : Red B B') : Red (.pi A B) (.pi A' B') :=
  (Red.map (fun x => .pi x B) .piA hA).trans (Red.map (fun x => .pi A' x) .piB hB)

theorem Red.ren {t t' : Tm} (h : Red t t') (ξ : Nat → Nat) : Red (t.ren ξ) (t'.ren ξ) :=
  Red.map (fun x => x.ren ξ) (fun hs => hs.ren ξ) h

theorem Red.subst {t t' : Tm} (h : Red t t') (σ : Nat → Tm) : Red (t.subst σ) (t'.subst σ) :=
  Red.map (fun x => x.subst σ) (fun hs => hs.subst σ) h

/-- Lifting a pointwise reduction of substitutions under a binder. -/
theorem Red.up {σ τ : Nat → Tm} (h : ∀ n, Red (σ n) (τ n)) : ∀ n, Red (Tm.up σ n) (Tm.up τ n)
  | 0 => .refl
  | n + 1 => (h n).ren Nat.succ

/-- **Reducing the substituted terms reduces the result.** -/
theorem Red.subst_red : ∀ (t : Tm) {σ τ : Nat → Tm}, (∀ n, Red (σ n) (τ n)) →
    Red (t.subst σ) (t.subst τ)
  | .var n, _, _, h => h n
  | .sort _, _, _, _ => .refl
  | .pi A B, _, _, h => Red.pi (Red.subst_red A h) (Red.subst_red B (Red.up h))
  | .lam A t, _, _, h => Red.lam (Red.subst_red A h) (Red.subst_red t (Red.up h))
  | .app t u, _, _, h => Red.app (Red.subst_red t h) (Red.subst_red u h)

/-- Both at once: reduce the term and the substituted terms. -/
theorem Red.subst2 {t t' : Tm} {σ τ : Nat → Tm} (ht : Red t t') (h : ∀ n, Red (σ n) (τ n)) :
    Red (t.subst σ) (t'.subst τ) :=
  (Red.subst_red t h).trans (ht.subst τ)

theorem Red.inst {t t' u u' : Tm} (ht : Red t t') (hu : Red u u') :
    Red (t.inst u) (t'.inst u') :=
  Red.subst2 ht (fun n => by cases n with | zero => exact hu | succ n => exact .refl)

/-! ## The shape of what a rigid term reduces to -/

theorem Red.sort_inv {s : Srt} {t : Tm} (h : Red (.sort s) t) : t = .sort s := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs Step.sort_inv

theorem Red.var_inv {n : Nat} {t : Tm} (h : Red (.var n) t) : t = .var n := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs Step.var_inv

theorem Red.pi_inv {A B t : Tm} (h : Red (.pi A B) t) :
    ∃ A' B', t = .pi A' B' ∧ Red A A' ∧ Red B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ hs ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      cases hs with
      | piA h => exact ⟨_, _, rfl, hA.tail h, hB⟩
      | piB h => exact ⟨_, _, rfl, hA, hB.tail h⟩

end LambdaLab.Languages.CoIC.DeBruijn
