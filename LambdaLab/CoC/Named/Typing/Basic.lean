import LambdaLab.CoC.Named.Step.Basic
import LambdaLab.TypeSystem.Named.Context

/-!
# The named CoC typing judgement

The de Bruijn rules in the named discipline's currency. What shifting did there, names do here
for free: `Lookup`'s accumulated shifts vanish (`get?` returns the type as written — its free
variables are *names*, valid in any context that binds them), and the `pi`/`lam` rules extend
the context by `cons`. Application instantiates the codomain by the capture-avoiding `subst`,
and `conv` re-types along joinability, exactly as on the other side.

## The recorded danger zone: shadowing in a dependent hashmap context

A named dependent context is where the hashmap representation meets its sharpest test.
`Γ.cons x A` *overwrites* any previous binding of `x` — harmless in STLC, where no type
mentions a variable — but here other entries' types may mention the old `x`, and after the
overwrite they silently refer to the new one. These rules state the natural named calculus and
do not guard against that; whether the guard is needed is precisely what the adequacy audit
against `CoC/DeBruijn` will decide when the translation and bridge arrive. Stating the rules
and letting the reference call them right or wrong is the methodology this repository runs on —
the named variant is the one under audit, and the docstring says so where the risk lives.
-/

namespace LambdaLab.CoC.Named

open LambdaLab.CoC (Srt)
open LambdaLab.Nominal (Atom)
open LambdaLab.TypeSystem.Named (Context)

variable {N : Type} [Atom N]

/-- The judgement. -/
inductive HasType : Context N (Term N) → Term N → Term N → Prop where
  /-- The axiom: `* : □`. Nothing types `□`. -/
  | ax : HasType Γ (.sort .prop) (.sort .typ)
  /-- No shifting: the stored type's free variables are names, good anywhere they're bound. -/
  | var : Γ.get? x = some A → HasType Γ (.var x) A
  /-- Product formation — all four PTS rule pairs, product in `s₂`. -/
  | pi : HasType Γ A (.sort s₁) → HasType (Γ.cons x A) B (.sort s₂) →
      HasType Γ (.pi x A B) (.sort s₂)
  /-- Abstraction, guarded by formation of its `Π`. -/
  | lam : HasType Γ (.pi x A B) (.sort s) → HasType (Γ.cons x A) b B →
      HasType Γ (.lam x A b) (.pi x A B)
  /-- Application instantiates the codomain, capture-avoidingly. -/
  | app : HasType Γ f (.pi x A B) → HasType Γ a A →
      HasType Γ (.app f a) (B.subst x a)
  /-- Conversion: β-equal types type the same terms. -/
  | conv : HasType Γ t A → Conv A B → HasType Γ B (.sort s) → HasType Γ t B

end LambdaLab.CoC.Named
