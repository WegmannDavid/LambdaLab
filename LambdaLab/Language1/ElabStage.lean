import LambdaLab.Language1.Elaboratable
import LambdaLab.Abstraction2.Basic

/-!
# Elaboration as a pipeline stage — why `ElaboratableLanguage`'s laws are the ones they are

`Abstraction2` stages compose into the front end: `List Char ⇝ List Token ⇝ Program`. This file
builds the *next* stage, `(written term, written type) ⇝ (its meaning)`, out of
`ElaboratableLanguage` and nothing else.

It exists as a justification, not for its own sake. The interface carries exactly three laws —
`elaborates_unique`, `elaborate_complete`, `quote_elaborates` — and each is consumed once below:

* the annotation over an elaborated `p` is the **fiber** of `Elaborates`, the surface forms that
  mean `p` (the same device the parser's truncation uses);
* `realize` is the fiber's first projection, so `abstract_realize` becomes "elaborate something
  from the fiber and land back on `p`" — which needs elaboration to *succeed*
  (`elaborate_complete`) and to be *single-valued* (`elaborates_unique`);
* `default` needs a canonical fiber member, which is `quote` together with the proof that what it
  writes lies in the fiber (`quote_elaborates`).

Removing any one of the three makes `elabStage` unbuildable; adding a fourth is not needed for it.
That is the sense in which the law set is right.
-/

namespace LambdaLab.Language1

open LambdaLab.Abstraction2

/-- **Elaboration as an `Abs` morphism**, at a fixed context. Concrete is what the author wrote —
a term and the type they declared for it; abstract is what it means; the annotation records the
surface forms that mean it. -/
def elabStage (L : ElaboratableLanguage) (Γ : Context (Var L.toLanguage) L.Ty) :
    Abstraction (L.Tm × L.Ty) (L.Tm × L.Ty)
      (fun p => { s : L.Tm × L.Ty // L.Elaborates Γ s.1 p.1 s.2 p.2 }) where
  abstract s := (L.elaborate Γ s.1 s.2).map (·.val)
  realize ann := ann.val
  default {p} := ⟨L.quote p.1 p.2, L.quote_elaborates Γ p.1 p.2⟩
  abstract_realize p ann := by
    show (L.elaborate Γ ann.val.1 ann.val.2).map (·.val) = some p
    have hsome := L.elaborate_complete ann.property
    cases hq : L.elaborate Γ ann.val.1 ann.val.2 with
    | none => rw [hq] at hsome; simp at hsome
    | some q =>
        obtain ⟨heq1, heq2⟩ := L.elaborates_unique q.property ann.property
        simp only [Option.map_some, Option.some.injEq]
        exact Prod.ext heq1 heq2

end LambdaLab.Language1
