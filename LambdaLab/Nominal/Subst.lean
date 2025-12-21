import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas

import LambdaLab.Nominal.Nominal

open Nominal

abbrev Substitution 𝕍 𝔻 [H : Ord 𝕍] := Std.TreeMap 𝕍 𝔻 H.compare

instance [Nominal 𝔻] : Nominal (Substitution Nat 𝔻) where
  fresh σ := σ.foldl (λ r a b ↦ max r (max a (fresh b))) 0


instance [H : Ord 𝕍] [ToString 𝕍] [ToString 𝔻] : ToString (Substitution 𝕍 𝔻) where
  toString σ := s!"{σ.toList}"

class Subst (𝕍 𝔻 𝕋 : Type) [H : Ord 𝕍] where
  subst : Substitution 𝕍 𝔻 → 𝕋 → 𝕋

def substOne [H : Ord 𝕍] [S : Subst 𝕍 𝔻 𝕋] (x : 𝕍) (d : 𝔻) (t : 𝕋) := S.subst {⟨ x, d ⟩} t


open Subst

instance SubstitutionIsSubst [H : Ord 𝕍] [Subst 𝕍 𝔼 𝔻] : Subst 𝕍 𝔼 (Substitution 𝕍 𝔻) where
  subst σ τ := τ.map (λ _ α ↦ subst σ α)

def chain [H : Ord 𝕍] [Subst 𝕍 𝔻 𝔻] (σ τ : Substitution 𝕍 𝔻) : Substitution 𝕍 𝔻 :=
  Std.TreeMap.mergeWith (λ _ _ s ↦ s) σ (subst σ τ)

@[simp]
theorem chain_subst [H : Ord 𝕍] [Subst 𝕍 𝔻 𝔻] [Subst 𝕍 𝔻 𝕋] (σ τ : Substitution 𝕍 𝔻) (t : 𝕋) :
  subst (chain σ τ) t = subst σ (subst τ t) := sorry

theorem subst_closed [Nominal 𝕋] [Subst Nat 𝔻 𝕋] (σ : Substitution Nat 𝔻) {t : 𝕋} : fresh t = 0 → subst σ t = t := by sorry
