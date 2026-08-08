import LambdaLab.Pipeline.Vernacular
import LambdaLab.TypeSystem.Context
import LambdaLab.Pipeline.Elaboratable

/-!
# Elaborating a whole program

`ElaboratableLanguage` says what one term means. This lifts that to a file: a fold of the
language's `Elaborates` through the declarations, threading the context left to right, together
with the algorithm computing it and the laws it inherits.

Everything here is derived. A language author supplies `Elaborates`/`elaborate`/`quote` for
*terms* and gets program elaboration — relation, algorithm, determinism, completeness, and
canonical printing — with no further obligation.

## The judgement relates two programs, not one

`Commands.Elaborates Γ cs cs'` says the written run `cs` elaborates to `cs'`. Elaborated commands
are `Command`s again: `def n : τ := e` becomes `def n : τ' := e'`. Reusing the same type is not
laziness — it is what makes the result printable by the very same vernacular parser, so the
elaborator's output can be rendered by `Language.renderProgram` with nothing new to write.

`WellTyped` is then just "elaborates to something".

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

namespace LambdaLab.Pipeline

open LambdaLab.TypeSystem (Context)

variable {L : ElaboratableLanguage}

/-! ## The judgement -/

/-- A run of commands elaborates when each one does, in the context its predecessors left behind,
contributing its *elaborated* type to the context for those that follow.

Threading left to right is what makes a declaration able to mention earlier ones and not later
ones — the vernacular has no mutual recursion. -/
inductive Commands.Elaborates (L : ElaboratableLanguage) :
    Context (Var L.toLanguage) L.Ty → List (Command L.toLanguage) →
    List (Command L.toLanguage) → Prop where
  | nil {Γ} : Commands.Elaborates L Γ [] []
  | cons {Γ n τ e e' τ' cs cs'} :
      L.Elaborates Γ e e' τ τ' →
      Commands.Elaborates L (Γ.cons n τ') cs cs' →
      Commands.Elaborates L Γ (Command.decl n τ e :: cs) (Command.decl n τ' e' :: cs')

/-- **A program elaborates** starting from the empty context: a file is closed, so nothing is in
scope until it is declared. -/
def Program.Elaborates (L : ElaboratableLanguage) (p p' : Program L.toLanguage) : Prop :=
  Commands.Elaborates L Context.empty p.toList p'.toList

/-- **Well-typed** = elaborates to something. -/
def Program.WellTyped (L : ElaboratableLanguage) (p : Program L.toLanguage) : Prop :=
  ∃ p', Program.Elaborates L p p'

/-! ## The algorithm

Structural on the command list; the context is a varying parameter, since each step extends it.
-/

/-- Elaborate a run of commands, carrying the derivation. -/
def Commands.elaborate (L : ElaboratableLanguage) :
    (Γ : Context (Var L.toLanguage) L.Ty) → (cs : List (Command L.toLanguage)) →
    Option { cs' // Commands.Elaborates L Γ cs cs' }
  | _, [] => some ⟨[], .nil⟩
  | Γ, .decl n τ e :: cs => do
      let q ← L.elaborate Γ e τ
      let r ← Commands.elaborate L (Γ.cons n q.val.2) cs
      some ⟨.decl n q.val.2 q.val.1 :: r.val, .cons q.property r.property⟩

/-- Elaborate a program. Non-emptiness is preserved by construction: the head command is
elaborated on its own, so the result is visibly a `cons`. -/
def Program.elaborate (L : ElaboratableLanguage) :
    (p : Program L.toLanguage) → Option { p' // Program.Elaborates L p p' }
  | (.decl n τ e, cs) => do
      let q ← L.elaborate Context.empty e τ
      let r ← Commands.elaborate L (Context.empty.cons n q.val.2) cs
      some ⟨(.decl n q.val.2 q.val.1, r.val), .cons q.property r.property⟩

/-! ## The laws, lifted

Each is the term-level law of `ElaboratableLanguage` threaded through the fold. Determinism is
what makes the threading well defined at all: without it the context after a command would not be
a function of the command.
-/

theorem Commands.elaborates_unique :
    ∀ {Γ cs cs₁ cs₂}, Commands.Elaborates L Γ cs cs₁ → Commands.Elaborates L Γ cs cs₂ →
      cs₁ = cs₂ := by
  intro Γ cs cs₁ cs₂ h₁ h₂
  induction h₁ generalizing cs₂ with
  | nil => cases h₂; rfl
  | cons he _ ih =>
      cases h₂ with
      | cons he₂ hcs₂ =>
          obtain ⟨rfl, rfl⟩ := L.elaborates_unique he he₂
          rw [ih hcs₂]

theorem Program.elaborates_unique {p p₁ p₂ : Program L.toLanguage}
    (h₁ : Program.Elaborates L p p₁) (h₂ : Program.Elaborates L p p₂) : p₁ = p₂ := by
  have h := Commands.elaborates_unique h₁ h₂
  obtain ⟨c₁, cs₁⟩ := p₁
  obtain ⟨c₂, cs₂⟩ := p₂
  simp only [NEList.toList, List.cons.injEq] at h
  exact Prod.ext h.1 h.2

theorem Commands.elaborate_complete :
    ∀ {Γ cs cs'}, Commands.Elaborates L Γ cs cs' → (Commands.elaborate L Γ cs).isSome := by
  intro Γ cs cs' h
  induction h with
  | nil => rfl
  | @cons Γ n τ e e' τ' cs cs' he _ ih =>
      -- the term elaborator succeeds, and lands on the same `τ'`, so the tail runs in exactly
      -- the context the derivation used, where the induction hypothesis applies
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (L.elaborate_complete he)
      obtain ⟨-, rfl⟩ := L.elaborates_unique he q.property
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp ih
      show (Commands.elaborate L Γ (Command.decl n τ e :: cs)).isSome
      rw [Commands.elaborate, hq]
      simp [hr]

theorem Program.elaborate_complete {p p' : Program L.toLanguage}
    (h : Program.Elaborates L p p') : (Program.elaborate L p).isSome := by
  obtain ⟨⟨n, τ, e⟩, cs⟩ := p
  obtain ⟨⟨n', τ', e'⟩, cs'⟩ := p'
  have h' : Commands.Elaborates L Context.empty (Command.decl n τ e :: cs)
      (Command.decl n' τ' e' :: cs') := h
  cases h' with
  | cons he hcs =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (L.elaborate_complete he)
      obtain ⟨-, rfl⟩ := L.elaborates_unique he q.property
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (Commands.elaborate_complete hcs)
      show (Program.elaborate L (Command.decl n τ e, cs)).isSome
      rw [Program.elaborate, hq]
      simp [hr]

/-! ## Writing an elaborated program back down -/

/-- The canonical surface form of an elaborated run: quote each command's term and type. -/
def Commands.quote (L : ElaboratableLanguage) :
    List (Command L.toLanguage) → List (Command L.toLanguage)
  | [] => []
  | .decl n τ' e' :: cs =>
      Command.decl n (L.quote e' τ').2 (L.quote e' τ').1 :: Commands.quote L cs

/-- …at program level. -/
def Program.quote (L : ElaboratableLanguage) :
    Program L.toLanguage → Program L.toLanguage
  | (.decl n τ' e', cs) =>
      (Command.decl n (L.quote e' τ').2 (L.quote e' τ').1, Commands.quote L cs)

/-- What `quote` writes elaborates back to what it came from. As at term level the hypothesis is
essential — an arbitrary run of commands need not be in the image of elaboration — and here it is
supplied by the derivation itself, which is exactly the form `Abstraction.default` needs. -/
theorem Commands.quote_elaborates :
    ∀ {Γ cs cs'}, Commands.Elaborates L Γ cs cs' →
      Commands.Elaborates L Γ (Commands.quote L cs') cs' := by
  intro Γ cs cs' h
  induction h with
  | nil => exact .nil
  | @cons Γ n τ e e' τ' cs cs' he _ ih =>
      exact .cons (L.quote_elaborates ⟨e, τ, he⟩) ih

theorem Program.quote_elaborates {p p' : Program L.toLanguage}
    (h : Program.Elaborates L p p') : Program.Elaborates L (Program.quote L p') p' := by
  obtain ⟨⟨n, τ', e'⟩, cs'⟩ := p'
  exact Commands.quote_elaborates h

end LambdaLab.Pipeline
