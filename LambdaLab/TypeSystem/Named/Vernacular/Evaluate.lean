import LambdaLab.TypeSystem.Named.Vernacular.Typing

/-!
# Running a program

`Elaborate.lean` turns a program into one with no metavariables left; this turns *that* into one
with no redexes left. Each declaration's body is replaced by its normal form, computed in the
context its predecessors built — the same context the typing judgement walks, for the same reason.

## What this is not

It is **β only**. A declaration's name enters the context, so later declarations mention it as a
free variable, and a body like `λ x . id ( id x )` is already normal: `id` is a variable, not a
value to unfold. Inlining earlier declarations (δ) would reduce further, and is deliberately not
done here — it is a different transformation, needing a term-substitution lemma this development
does not have, and it is not what `HasEval` supplies.

## Why the derivation is threaded through

`HasEval.eval` takes the typing derivation, because that is where strong normalization comes from.
That does *not* make `evalCommands` a large elimination: it recurses on the command **list**, and
the derivation is passed along as an ordinary argument and taken apart only by the `Prop`-valued
inversion lemmas below. Lean's definitional proof irrelevance then makes the result independent of
*which* derivation was supplied, which is what lets the theorems below quantify over it freely.

## The three facts

Evaluation lands in the image and fixes it: the result is well-typed (`evalCommands_hasType`),
every body is normal (`evalCommands_normalBodies`), and a program already in that state is left
alone (`evalCommands_of_normalBodies`). The last is what an `Abstraction` needs for its canonical
annotation, and the first is what stops the result from being a program the vernacular rejects —
groundness is the delicate half of it, and rests on `LawfulHasEval.evalGround`.
-/

namespace LambdaLab.TypeSystem.Named.Vernacular

open HasVars (Ground)
open LambdaLab.Nominal (Atom)

/-! Only `[LawfulHasEval]`, and no bare `[HasType]` beside it. A separate `HasType` variable would
be a *second*, unrelated judgement: the derivations the inversion lemmas produce would not be the
ones `HasEval.eval` accepts, and every application below is a type error. Same discipline as
`Elaborate.lean`, which takes `[PrincipalElaborate]` alone for the same reason. -/

variable {N Tm Ty : Type} [Atom N] [LawfulHasEval N Tm Ty]

/-! ## Inverting the judgement

Both are `Prop → Prop`, so `cases` on the derivation is allowed; nothing here builds data out of
it. They exist so that `evalCommands` can name the two things it needs without repeating the
`cases`. -/

/-- The head declaration's body has its declared type. -/
theorem HasTypeGround.head_typed {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) :
    _root_.LambdaLab.TypeSystem.Named.HasType.HasType Γ t τ := by
  cases h with | decl ht _ _ _ => exact ht

/-- The head declaration's body is ground. -/
theorem HasTypeGround.head_ground {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) : Ground t := by
  cases h with | decl _ _ hg _ => exact hg

/-- The head declaration's type is ground. -/
theorem HasTypeGround.head_tyGround {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) : Ground τ := by
  cases h with | decl _ hτ _ _ => exact hτ

/-- The rest of the program types in the extended context. -/
theorem HasTypeGround.tail {Γ : Context N Ty} {x : N} {τ : Ty} {t : Tm}
    {cs : List (Command N Tm Ty)} (h : HasTypeGround Γ (Command.decl x τ t :: cs)) :
    HasTypeGround (Γ.cons x τ) cs := by
  cases h with | decl _ _ _ hcs => exact hcs

/-- The empty program's context is ground — the `nil` constructor, inverted. -/
theorem HasTypeGround.nil_ctxGround {Γ : Context N Ty} (h : HasTypeGround Γ ([] : List (Command N Tm Ty))) :
    CtxGround Γ := by
  cases h with | nil hg => exact hg

/-! ## Normal bodies -/

/-- Every declaration body admits no further reduction. The image of `evalCommands`. -/
def NormalBodies : List (Command N Tm Ty) → Prop
  | [] => True
  | Command.decl _ _ t :: cs => NormalForm t ∧ NormalBodies cs

/-- A whole program is normal when its command list is. -/
abbrev AllNormal (p : Program N Tm Ty) : Prop :=
  NormalBodies p.toList

/-! ## The evaluator -/

/-- **Normalize every body**, each in the context its predecessors built. -/
def evalCommands : (Γ : Context N Ty) → (cs : List (Command N Tm Ty)) → HasTypeGround Γ cs →
    List (Command N Tm Ty)
  | _, [], _ => []
  | Γ, Command.decl x τ t :: cs, h =>
      Command.decl x τ (HasEval.eval Γ t τ h.head_typed) :: evalCommands (Γ.cons x τ) cs h.tail

/-- **The result is still a well-typed program.** Types survive by `preservation_mstep` along
`evalReachable`; groundness — the half nothing else in the tower gives — by
`LawfulHasEval.evalGround`. -/
theorem evalCommands_hasType : ∀ (Γ : Context N Ty) (cs : List (Command N Tm Ty))
    (h : HasTypeGround Γ cs), HasTypeGround Γ (evalCommands Γ cs h)
  | _, [], h => h
  | Γ, Command.decl x τ _t :: cs, h =>
      HasTypeGround.decl
        (preservation_mstep h.head_typed (LawfulHasEval.evalReachable h.head_typed))
        h.head_tyGround
        (LawfulHasEval.evalGround h.head_typed h.head_ground)
        (evalCommands_hasType (Γ.cons x τ) cs h.tail)

/-- **The result is normal** — `evalNormal`, declaration by declaration. -/
theorem evalCommands_normalBodies : ∀ (Γ : Context N Ty) (cs : List (Command N Tm Ty))
    (h : HasTypeGround Γ cs), NormalBodies (evalCommands Γ cs h)
  | _, [], _ => trivial
  | Γ, Command.decl x τ _t :: cs, h =>
      ⟨LawfulHasEval.evalNormal h.head_typed, evalCommands_normalBodies (Γ.cons x τ) cs h.tail⟩

/-- **Evaluation fixes what it has already reached.** `eval_of_normalForm`, declaration by
declaration — the statement an `Abstraction`'s canonical annotation needs. -/
theorem evalCommands_of_normalBodies : ∀ (Γ : Context N Ty) (cs : List (Command N Tm Ty))
    (h : HasTypeGround Γ cs), NormalBodies cs → evalCommands Γ cs h = cs
  | _, [], _, _ => rfl
  | Γ, Command.decl x τ t :: cs, h, hn => by
      show Command.decl x τ (HasEval.eval Γ t τ h.head_typed) :: evalCommands (Γ.cons x τ) cs h.tail
        = Command.decl x τ t :: cs
      rw [eval_of_normalForm h.head_typed hn.1,
        evalCommands_of_normalBodies (Γ.cons x τ) cs h.tail hn.2]

/-! ## At the level of programs

`Program` is a `NEList`, i.e. a head and a tail, and `evalCommands` never shortens a list — so the
evaluated program is non-empty for the same reason the input was, and the head/tail split survives
without a separate argument. -/

/-- **Normalize a program.** The match is on the head/tail pair rather than on `toList`, so the
result is a `Program` by construction — `evalCommands` never shortens a list, but saying so would
be an extra lemma where matching the pair is none. -/
def evalProgram : (p : Program N Tm Ty) → HasType p → Program N Tm Ty
  | (Command.decl x τ t, cs), h =>
      (Command.decl x τ (HasEval.eval Context.empty t τ h.head_typed),
        evalCommands ((Context.empty : Context N Ty).cons x τ) cs h.tail)

/-- The normalized program is still well-typed. -/
theorem evalProgram_hasType : ∀ (p : Program N Tm Ty) (h : HasType p),
    HasType (evalProgram p h)
  | (Command.decl x τ _t, cs), h =>
      HasTypeGround.decl
        (preservation_mstep h.head_typed (LawfulHasEval.evalReachable h.head_typed))
        h.head_tyGround
        (LawfulHasEval.evalGround h.head_typed h.head_ground)
        (evalCommands_hasType ((Context.empty : Context N Ty).cons x τ) cs h.tail)

/-- Every body of the normalized program is a normal form. -/
theorem evalProgram_allNormal : ∀ (p : Program N Tm Ty) (h : HasType p),
    AllNormal (evalProgram p h)
  | (Command.decl x τ _t, cs), h =>
      ⟨LawfulHasEval.evalNormal h.head_typed,
        evalCommands_normalBodies ((Context.empty : Context N Ty).cons x τ) cs h.tail⟩

/-- **The fixed point.** A program whose bodies are already normal is returned unchanged — which is
what lets an `Abstraction` whose target is the normalized programs take each value as its own
canonical re-presentation. -/
theorem evalProgram_of_allNormal : ∀ (p : Program N Tm Ty) (h : HasType p),
    AllNormal p → evalProgram p h = p
  | (Command.decl x τ t, cs), h, hn => by
      show ((Command.decl x τ (HasEval.eval Context.empty t τ h.head_typed) :
              Command N Tm Ty), evalCommands _ cs h.tail) = (Command.decl x τ t, cs)
      rw [eval_of_normalForm h.head_typed hn.1,
        evalCommands_of_normalBodies ((Context.empty : Context N Ty).cons x τ) cs h.tail hn.2]

end LambdaLab.TypeSystem.Named.Vernacular
