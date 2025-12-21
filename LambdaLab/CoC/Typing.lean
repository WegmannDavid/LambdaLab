import LambdaLab.CoC.Tm
import LambdaLab.CoC.Vernacular
import LambdaLab.Nominal.Context

open Subst

inductive Typing : Context Tm → Tm → Tm → Prop where
| typ :

  ------------------------------
  Typing Γ (.typ u) (.typ (u+1))

| var :

  Contains Γ x α →
  -----------------
  Typing Γ (# x) α

| app :

  Typing Γ t (Π x : α  => β) →
  Typing Γ s α →
  -----------------------------------
  Typing Γ (t ⬝ s) (subst {⟨x, s⟩} β)

| prd :

  Typing Γ α (.typ u) →
  Typing (push Γ x α) β (.typ v) →
  Typing Γ (Π x : α => β) (.typ v)

| abs :

  Typing Γ α (.typ u) →
  Typing (push Γ x α) t β →
  --------------------------------------
  Typing Γ (ƛ x : α => t) (Π x : α => β)

| beta :

  Typing Γ α (.typ u) →
  -- add α reduces to α'
  Typing Γ t α' →
  -----------------------
  Typing Γ t α

notation:min Γ "⊢" t ":" α => Typing Γ t α
