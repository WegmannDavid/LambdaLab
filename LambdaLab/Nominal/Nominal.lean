
class Nominal (α : Type) where
  fresh  : α → Nat

open Nominal

--instance [Nominal A] [Nominal B] : Nominal (A × B) where
--  fresh := λ ⟨ a, b ⟩ ↦ max (fresh a) (fresh b)

def fresh2 [Nominal A] [Nominal B] (a : A) (b : B) := max (fresh a) (fresh b)
def fresh3 [Nominal A] [Nominal B] [Nominal C] (a : A) (b : B) (c : C) := max (fresh2 a b) (fresh c)
def fresh4 [Nominal A] [Nominal B] [Nominal C] [Nominal D] (a : A) (b : B) (c : C) (d : D)  := max (fresh3 a b c) (fresh d)
