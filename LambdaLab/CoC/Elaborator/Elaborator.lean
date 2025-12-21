import LambdaLab.Coc.Typing
import LambdaLab.Coc.Elaborator.Unify

open Nominal Subst Coc.Elaborator

inductive EnsureResult (Γ : Context Ty) (x : String) (α : Ty) where
| result : ∀ (σ : Substitution Nat Ty), Contains (subst σ Γ) x (subst σ α) → EnsureResult Γ x α

def ensure (Γ : Context Ty) (x : String) (α : Ty) : Except String (EnsureResult Γ x α) :=
    match Heq : Γ[x]? with
    | some α' => match unify α α' with
                 | some ⟨ σ, Heq' ⟩ => .ok ⟨ σ, by rw[Heq']; sorry ⟩
                 | none => .error s!"unification of {α} with {α'} failed"
    | none    => .error s!"the context does not contain the variable {x}"

def elaborateTm (σ : Substitution Nat Ty) (Γ : Context Ty) (t : Tm) (γ : Ty)
  : Except String { δ : Substitution Nat Ty // (subst δ Γ ⊢ subst δ (subst σ t) : subst δ γ) } :=
  match t with
  | .var x     => do
    let ⟨ δ, H ⟩ ← ensure Γ x γ
    return ⟨ δ, .var H ⟩
  | .app t s   => do
    let α := .var (fresh4 σ Γ t γ)
    let ⟨ δ, Ht ⟩ ← elaborateTm σ Γ t (α ⟶ γ)
    let σ' := chain δ σ
    let Γ' := subst δ Γ
    let α' := subst δ α
    let ⟨ δ', Hs ⟩ ← elaborateTm σ' Γ' s α'
    let σ'' := chain δ' σ'
    let Γ'' := subst δ' Γ'
    let Ht' := Typing_subst δ' Ht
    return ⟨ chain δ' δ, by
      rw[chain_subst] at Hs
      simp
      simp at Ht'
      constructor
      . apply Ht'
      . apply Hs
     ⟩
  | .abs x α t => do
    let β := .var (fresh4 σ Γ t γ)
    let ⟨ δ, eαβγ ⟩ ← unifyE ((subst σ α) ⟶ β) γ
    let σ' := chain δ σ
    let β' := subst δ β
    let α' := subst δ (subst σ α)
    let Γ' := subst δ Γ
    let ⟨ δ', Ht ⟩ ← elaborateTm σ' (push Γ' x α') t β'
    return ⟨ chain δ' δ, by
      simp
      rw[<-eαβγ]
      constructor
      rw[push_subst, chain_subst] at Ht
      apply Ht ⟩

def elaborate (t : Tm) : Except String ((Substitution Nat Ty) × Ty) := do
    let γ := .var (fresh t)
    let ⟨ δ, _ ⟩ ← elaborateTm ∅ ∅ t γ
    return ⟨ δ, subst δ γ ⟩

def checkClosed [Nominal α] [ToString α] (t : α) : Except String (PLift (fresh t = 0)) :=
  if H : fresh t = 0 then .ok ⟨ H ⟩ else .error s!"Could not infer all variables in {t}"

def elaborateVernacular (Γ : Context Ty) (Γ_closed : fresh Γ = 0) (v : Vernacular) : Except String ({ v' // TypingVernacular Γ v'}) :=
    match v with
    | []          => .ok ⟨ [], .eof ⟩
    | ⟨ x, α, t ⟩::ds => do
      let ⟨ δ, Ht ⟩ ← elaborateTm ∅ Γ t α
      let Γ' := subst δ Γ
      let t' := subst δ t
      let α' := subst δ α
      let α'_closed ← checkClosed α'
      let ⟨ ds', Hds ⟩  ← elaborateVernacular (push Γ' x α') (by sorry) ds
      let H' := (subst_closed δ Γ_closed)
      return ⟨ ⟨ x, α', t' ⟩::ds' , sorry ⟩
