import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import LambdaLab.Nominal.Subst

/-- A key-value structure with String keys and generic values. -/
abbrev Context 𝕋 := Std.TreeMap String 𝕋

open Subst

instance [Subst Nat 𝔻 𝕋] : Subst Nat 𝔻 (Context 𝕋) where
  subst σ Γ := Γ.map (λ _ ↦ (subst σ))

open Nominal
instance [Nominal α]  : Nominal (Context α) where
  fresh Γ := Γ.foldl (λ r _ v ↦ max r (fresh v)) 0

def push (Γ : Context α) (x : String) (v : α) : Context α :=
  Std.TreeMap.insert Γ x v

@[simp]
theorem push_subst [Subst Nat 𝔻 𝕋] {σ : Substitution Nat 𝔻} {Γ : Context 𝕋} :
  subst σ (push Γ k v) = push (subst σ Γ) k (subst σ v) := sorry



def Contains (Γ : Context α) (x : String) (v : α) : Prop := Γ[x]? = some v

def checkContains [DecidableEq α] (Γ : Context α) x v : Option (PLift (Contains Γ x v)) :=
  match e1 : Γ[x]? with
  | some v' => if e2 : v = v' then some ⟨ (e2.symm) ▸ e1 ⟩ else none
  | none    => none


theorem context_push_contains : Contains (push Γ x α) x α := Std.TreeMap.getElem?_insert_self


/-
/-- Insert a key-value pair into the StringMap. -/
def insert {α : Type} (m : Context α) (k : String) (v : α) : Context α :=
  Batteries.RBMap.insert m k v

def erase {α : Type} (m : Context α) (k : String) : Context α :=
  Batteries.RBMap.erase m k

def Lookup {α : Type} (m : Context α) (k : String) (v : α) := m.find? k = some v

/-- Lookup a value in the StringMap. -/
def lookup {α : Type} (m : Context α) (k : String) : Option ({ v // Lookup m k v}) :=
  match H : m.find? k with
  | some v => some ⟨ v, H ⟩
  | none   => none

end Context
-/
