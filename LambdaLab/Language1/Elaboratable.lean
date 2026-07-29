import LambdaLab.Language1.Basic
import LambdaLab.Language1.Context

/-!
# `ElaboratableLanguage` — a language whose programs can be given meaning

A `Language` says how to read and print a program. This says how to *elaborate* one: turn a
surface term, checked against an expected type, into the term and type it means.

## Synthetic on purpose

Nothing about substitutions, unification or principal types appears here. `Elaborates` is an
abstract relation between what was written and what it means; a language inferring types by
Hindley–Milner keeps all the `Subst`/`mgu` machinery *inside* its own instance, and the
vernacular never sees it. There is no `HasType` field either — `Elaborates` subsumes it, since
relating a term to its type is what typing is.

## Metavariable leakage is the language's business, not this interface's

Whether an unsolved metavariable may survive a declaration is decided by the language, in the
relation it supplies: to forbid leaking, do not let `Elaborates` relate anything to an
unresolved output, and such a declaration then simply fails to elaborate. Nothing here needs a
`Resolved` predicate to say so.

## Why exactly these laws

The laws are the ones that make elaboration a stage of the `Abstraction2` pipeline — no more.
Reading them off `Abstraction`'s fields with the annotation over an elaborated `t'` taken to be
its **fiber** (`{ t // Elaborates Γ t t' τ τ' }`, the surface forms meaning it, exactly as the
parser's truncation does):

* `abstract` is `elaborate`, and its soundness is carried by the subtype it returns;
* `abstract_realize` — realize an annotation and re-elaborate, recovering the same value — needs
  `elaborate` to *succeed* on anything in the fiber (`elaborate_complete`) and to land on the
  *same* answer (`elaborates_unique`);
* `default` needs a canonical member of every fiber: `quote` writes an elaborated term back down,
  and `quote_elaborates` is exactly the statement that what it writes is in the fiber.

So: determinism, completeness, and a canonical inverse. Nothing else is forced, and nothing else
is here.
-/

namespace LambdaLab.Language1

/-- A `Language` together with its semantics: an elaboration relation, an algorithm establishing
it, and enough structure to run it backwards. -/
structure ElaboratableLanguage extends Language where
  /-- `Elaborates Γ t t' τ τ'`: under `Γ`, the surface term `t` checked against the expected type
  `τ` elaborates to the term `t'` of type `τ'`.

  Both a typing judgement and an elaboration: `τ` may be less informative than `τ'` — it can be a
  metavariable the language solves — and `t'` may differ from `t` by exactly the information that
  was recovered. -/
  Elaborates : Context (Var toLanguage) Ty → Tm → Tm → Ty → Ty → Prop

  /-- **Elaboration is deterministic.** One surface term checked at one expected type has at most
  one meaning. Without this, `abstract` could not be a function on the fiber, and the pipeline
  stage's round-trip law would be unstatable. -/
  elaborates_unique : ∀ {Γ t τ t₁ τ₁ t₂ τ₂},
    Elaborates Γ t t₁ τ τ₁ → Elaborates Γ t t₂ τ τ₂ → t₁ = t₂ ∧ τ₁ = τ₂

  /-- The algorithm. `none` means the term does not elaborate at that type; a success carries the
  result *with* its certificate, so soundness needs no separate law. -/
  elaborate : (Γ : Context (Var toLanguage) Ty) → (t : Tm) → (τ : Ty) →
    Option { p : Tm × Ty // Elaborates Γ t p.1 τ p.2 }

  /-- **…and it does not miss.** If anything elaborates, the algorithm finds it. This is what lets
  `abstract` succeed on every surface form in a fiber. -/
  elaborate_complete : ∀ {Γ t τ t' τ'},
    Elaborates Γ t t' τ τ' → (elaborate Γ t τ).isSome

  /-- **Writing an elaborated term back down**: the canonical surface form of `t' : τ'`. This is
  the `default` annotation of the pipeline stage — the form a printer would emit. -/
  quote : Tm → Ty → Tm × Ty

  /-- …and what it writes really does mean what it came from. `abstract_realize` at `default`. -/
  quote_elaborates : ∀ (Γ : Context (Var toLanguage) Ty) (t' : Tm) (τ' : Ty),
    Elaborates Γ (quote t' τ').1 t' (quote t' τ').2 τ'

end LambdaLab.Language1
