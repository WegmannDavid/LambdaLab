import LambdaLab.CoC.DeBruijn.Step.Basic

/-!
# The CoC typing judgement

Dependent typing changes the judgement's furniture in three ways, each visible below:

* **Lookup shifts as it walks.** The type at index `n` was written in the context that existed
  `n + 1` binders ago, so retrieving it must shift it past everything since. The shifts are
  built into `Lookup`'s two constructors — `here` already shifts once — rather than patched on
  at the use site.
* **Formation is part of typing.** `Π` and `λ` demand their pieces well-sorted: CoC is the full
  PTS — all four `(s₁, s₂)` rule pairs are allowed, with the product landing in `s₂` — which is
  what makes `Π(A:*). …` (System F's `∀`) and `Π(x:A). …` (the simple arrow) the *same rule*.
* **Conversion.** Application substitutes terms into types, so types compute, and a judgement
  that cannot follow β-equal types apart from syntactic equality would reject well-typed terms.
  `conv` re-types along `Conv` (joinability), guarded by well-sortedness of the target.

The axiom is `* : □`, and `□` is untypeable — pure CoC, no universe hierarchy. Contexts are the
tower's `List Term`, so the judgement instantiates `TypeSystem.DeBruijn.HasType Term Term`:
one carrier in both slots, the collapse `Basic.lean`'s header advertises.
-/

namespace LambdaLab.CoC.DeBruijn

/-- A typing context: the types (which are terms) of the variables in scope. -/
abbrev Ctx := List Term

/-- Positional lookup, shifting as it walks: the retrieved type is stated in *today's* context,
not the one it was written in. -/
inductive Lookup : Ctx → Nat → Term → Prop where
  | here  : Lookup (A :: Γ) 0 (A.shift 0)
  | there : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (A.shift 0)

/-- The judgement. -/
inductive HasType : Ctx → Term → Term → Prop where
  /-- The axiom: `* : □`. Nothing types `□`. -/
  | ax : HasType Γ (.sort .prop) (.sort .typ)
  | var : Lookup Γ n A → HasType Γ (.var n) A
  /-- Product formation — all four PTS rule pairs, product in `s₂`: dependent and simple
  function spaces, over terms and over types, one rule. -/
  | pi : HasType Γ A (.sort s₁) → HasType (A :: Γ) B (.sort s₂) →
      HasType Γ (.pi A B) (.sort s₂)
  /-- Abstraction, guarded by formation of its `Π`. -/
  | lam : HasType Γ (.pi A B) (.sort s) → HasType (A :: Γ) b B →
      HasType Γ (.lam A b) (.pi A B)
  /-- Application instantiates the codomain — the rule that makes types compute. -/
  | app : HasType Γ f (.pi A B) → HasType Γ a A →
      HasType Γ (.app f a) (B.subst 0 a)
  /-- Conversion: β-equal types type the same terms, well-sortedness of the target as guard. -/
  | conv : HasType Γ t A → Conv A B → HasType Γ B (.sort s) → HasType Γ t B

/-- CoC keeps its own turnstile for the family's usual reason: the context type (`List Term` of
*this* `Term`) disambiguates it from every other `⊢` in scope. -/
notation:40 Γ:41 " ⊢ " t:41 " : " A:41 => HasType Γ t A

end LambdaLab.CoC.DeBruijn
