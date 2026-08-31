import LambdaLab.SysF.DeBruijn.Basic

/-!
# The System F typing judgement

Contexts are lists of types, as STLC's are — which is what lets this calculus instantiate the
de Bruijn tower unchanged. The new content is in two rules:

* `tlam` — going under a `Λ` shifts every type in the context (`Γ.map (Ty.shift 0)`): the
  context's types now live one type-binder deeper, and their variables must say so;
* `tapp` — `∀`-elimination is `Ty.subst` at index `0`: the instantiated body.

**No type-variable scoping.** The judgement never checks that a `Ty.var` is bound: a free type
variable types like an opaque base type, exactly as STLC's `Ty.mvar` does in its judgement.
`Basic.lean`'s header says why this is a design and not an omission — it is the hinge of the
STLC embedding (`Embed.lean`), where `mvar n ↦ var n` carries the STLC rules onto these rules
clause for clause.
-/

namespace LambdaLab.SysF.DeBruijn

/-- A typing context: the types of the term variables in scope, most recent binder first. -/
abbrev Ctx := List Ty

/-- Positional lookup, as in STLC. -/
inductive Lookup : Ctx → Nat → Ty → Prop where
  | here  : Lookup (τ :: Γ) 0 τ
  | there : Lookup Γ n τ → Lookup (τ' :: Γ) (n + 1) τ

/-- The judgement. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var : Lookup Γ n τ → HasType Γ (.var n) τ
  | lam : HasType (τ₁ :: Γ) e τ₂ → HasType Γ (.lam τ₁ e) (τ₁ ⇒ τ₂)
  | app : HasType Γ e₁ (τ₁ ⇒ τ₂) → HasType Γ e₂ τ₁ → HasType Γ (.app e₁ e₂) τ₂
  /-- Under a `Λ`, the context's types shift: they live one type-binder deeper now. -/
  | tlam : HasType (Γ.map (Ty.shift 0)) e τ → HasType Γ (.tlam e) (.all τ)
  /-- `∀`-elimination: the body, instantiated. -/
  | tapp : HasType Γ e (.all τ) → HasType Γ (.tapp e σ) (τ.subst 0 σ)

/-- System F keeps its own turnstile, for the reason STLC's de Bruijn variant does: the context
is a `List Ty` of its own `Ty`, so the type of `Γ` disambiguates it from every other `⊢` in
scope. Argument levels pinned so `Γ ⊢ e : τ → P` splits at the arrow. -/
notation:40 Γ:41 " ⊢ " e:41 " : " τ:41 => HasType Γ e τ

end LambdaLab.SysF.DeBruijn
