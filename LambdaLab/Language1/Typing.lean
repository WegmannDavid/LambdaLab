import LambdaLab.Language1.Vernacular
import LambdaLab.Language1.Context
import LambdaLab.Language1.Elaboratable

/-!
# When is a program well-typed?

A fold of the language's `Elaborates` relation through the declarations, threading the context
left to right. Nothing algorithmic lives here — this says what the elaborator has to establish,
not how it does so.

## The context receives the *elaborated* type

`def n : τ := e` contributes `n : τ'`, not `n : τ`. The written `τ` is what the author asked for
and may be less informative than the truth — it can contain metavariables the language solves
while checking `e`. `τ'` is what came back.

Whether a metavariable may leak from one declaration to the next is therefore decided entirely by
the language's `Elaborates`: a language that refuses to relate anything to an unresolved output
rejects `def f : ?0 → ?0 := λ x : ?0 . x` outright — not by a side condition here, but because
nothing determines a `τ'` for it. A language that wants leaking simply permits it. This file
takes no position.
-/

namespace LambdaLab.Language1

/-- A run of commands is well-typed when each one elaborates in the context its predecessors left
behind, and contributes its elaborated type to the context for those that follow.

Threading left to right is what makes a declaration able to mention earlier ones and not later
ones — the vernacular has no mutual recursion. -/
inductive Commands.WellTyped (L : ElaboratableLanguage) :
    Context (Var L.toLanguage) L.Ty → List (Command L.toLanguage) → Prop where
  | nil {Γ} : Commands.WellTyped L Γ []
  | cons {Γ n τ e e' τ' cs} :
      L.Elaborates Γ e e' τ τ' →
      Commands.WellTyped L (Γ.cons n τ') cs →
      Commands.WellTyped L Γ (Command.decl n τ e :: cs)

/-- **A program is well-typed** when its commands are, starting from the empty context: a file is
closed, so nothing is in scope until it is declared. -/
def Program.WellTyped (L : ElaboratableLanguage) (p : Program L.toLanguage) : Prop :=
  Commands.WellTyped L Context.empty p.toList

end LambdaLab.Language1
