import LambdaLab.Languages.CoIC.DeBruijn.Syntax
import LambdaLab.Relation.Closure
import LambdaLab.Relation.Normalization

/-!
# CoC with inductive types — reduction

Full β-reduction, plus ι: a recursor applied to a constructor steps to the constructor's branch,
applied to the constructor's arguments and to the recursive calls on its recursive ones
(`Tm.iotaRhs`). Both may fire anywhere — under binders, inside domains and annotations, inside
argument and branch lists. `Red` is the reflexive-transitive closure.

ι asks that the branch and argument lists be well-formed lists (`Tm.isList`); that is what keeps
it stable under substitution — a variable standing for a list could otherwise become one.

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
  | iota {i k : Nat} {mask : List Bool} {C bs as : Tm} : bs.isList = true → as.isList = true →
      Step (.elim i C bs (.ctor i k mask as)) (Tm.iotaRhs i C bs k mask as)
  | ctorA {i k : Nat} {mask : List Bool} {as as' : Tm} : Step as as' →
      Step (.ctor i k mask as) (.ctor i k mask as')
  | elimC {i : Nat} {C C' bs t : Tm} : Step C C' → Step (.elim i C bs t) (.elim i C' bs t)
  | elimB {i : Nat} {C bs bs' t : Tm} : Step bs bs' → Step (.elim i C bs t) (.elim i C bs' t)
  | elimT {i : Nat} {C bs t t' : Tm} : Step t t' → Step (.elim i C bs t) (.elim i C bs t')
  | consH {a a' l : Tm} : Step a a' → Step (.tcons a l) (.tcons a' l)
  | consT {a l l' : Tm} : Step l l' → Step (.tcons a l) (.tcons a l')

/-- Many steps. -/
abbrev Red : Tm → Tm → Prop := RTC Step

theorem Step.var_inv {n : Nat} {t : Tm} : ¬ Step (.var n) t := nofun

theorem Step.sort_inv {s : Srt} {t : Tm} : ¬ Step (.sort s) t := nofun

theorem Step.ind_inv {i : Nat} {t : Tm} : ¬ Step (.ind i) t := nofun

theorem Step.tnil_inv {t : Tm} : ¬ Step .tnil t := nofun

/-- Reduction keeps an argument list a list. -/
theorem Step.isList {l l' : Tm} (h : Step l l') (hl : l.isList = true) : l'.isList = true := by
  induction h with
  | consT _ ih => exact ih hl
  | _ => simp_all [Tm.isList]

/-- **A step inside an argument list is a step at one position**, the others unchanged. -/
theorem Step.list_inv {l l' : Tm} (h : Step l l') (hl : l.isList = true) :
    l'.toList.length = l.toList.length ∧
      ∃ j, Step (l.nth j) (l'.nth j) ∧ ∀ j', j' ≠ j → l'.nth j' = l.nth j' := by
  induction h with
  | @consH a a' r h' =>
      refine ⟨rfl, 0, h', fun j' hj' => ?_⟩
      cases j' with
      | zero => exact absurd rfl hj'
      | succ j' => rfl
  | @consT a r r' h' ih =>
      obtain ⟨hlen, j, hj, heq⟩ := ih hl
      refine ⟨by simp [Tm.toList, hlen], j + 1, hj, fun j' hj' => ?_⟩
      cases j' with
      | zero => rfl
      | succ j' => exact heq j' (fun e => hj' (by rw [e]))
  | _ => simp [Tm.isList] at hl

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
  | iota hb ha =>
      intro ξ
      rw [Tm.iotaRhs_ren _ _ hb ha]
      exact .iota (Tm.isList_ren _ _ hb) (Tm.isList_ren _ _ ha)
  | ctorA _ ih => intro ξ; exact .ctorA (ih ξ)
  | elimC _ ih => intro ξ; exact .elimC (ih ξ)
  | elimB _ ih => intro ξ; exact .elimB (ih ξ)
  | elimT _ ih => intro ξ; exact .elimT (ih ξ)
  | consH _ ih => intro ξ; exact .consH (ih ξ)
  | consT _ ih => intro ξ; exact .consT (ih ξ)

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
  | iota hb ha =>
      intro σ
      rw [Tm.iotaRhs_subst _ _ hb ha]
      exact .iota (Tm.isList_subst _ _ hb) (Tm.isList_subst _ _ ha)
  | ctorA _ ih => intro σ; exact .ctorA (ih σ)
  | elimC _ ih => intro σ; exact .elimC (ih σ)
  | elimB _ ih => intro σ; exact .elimB (ih σ)
  | elimT _ ih => intro σ; exact .elimT (ih σ)
  | consH _ ih => intro σ; exact .consH (ih σ)
  | consT _ ih => intro σ; exact .consT (ih σ)

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

theorem Red.ctor {i k : Nat} {mask : List Bool} {as as' : Tm} (h : Red as as') :
    Red (.ctor i k mask as) (.ctor i k mask as') :=
  Red.map (fun x => .ctor i k mask x) .ctorA h

theorem Red.elim {i : Nat} {C C' bs bs' t t' : Tm} (hC : Red C C') (hb : Red bs bs')
    (ht : Red t t') : Red (.elim i C bs t) (.elim i C' bs' t') :=
  ((Red.map (fun x => .elim i x bs t) .elimC hC).trans
    (Red.map (fun x => .elim i C' x t) .elimB hb)).trans
    (Red.map (fun x => .elim i C' bs' x) .elimT ht)

theorem Red.tcons {a a' l l' : Tm} (ha : Red a a') (hl : Red l l') :
    Red (.tcons a l) (.tcons a' l') :=
  (Red.map (fun x => .tcons x l) .consH ha).trans (Red.map (fun x => .tcons a' x) .consT hl)

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
  | .ind _, _, _, _ => .refl
  | .ctor _ _ _ as, _, _, h => Red.ctor (Red.subst_red as h)
  | .elim _ C bs t, _, _, h =>
      Red.elim (Red.subst_red C h) (Red.subst_red bs h) (Red.subst_red t h)
  | .tnil, _, _, _ => .refl
  | .tcons a l, _, _, h => Red.tcons (Red.subst_red a h) (Red.subst_red l h)

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

theorem Red.ind_inv {i : Nat} {t : Tm} (h : Red (.ind i) t) : t = .ind i := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs Step.ind_inv

theorem Red.isList {l l' : Tm} (h : Red l l') (hl : l.isList = true) : l'.isList = true := by
  induction h with
  | refl => exact hl
  | tail _ hs ih => exact hs.isList ih

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
