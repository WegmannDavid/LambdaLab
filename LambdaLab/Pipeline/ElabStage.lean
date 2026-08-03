import LambdaLab.Pipeline.Elaboratable
import LambdaLab.Abstraction.Basic
import LambdaLab.Pipeline.Typing
import LambdaLab.Pipeline.Pipeline

/-!
# Elaboration as a pipeline stage — why `ElaboratableLanguage`'s laws are the ones they are

`Abstraction` stages compose into the front end: `List Char ⇝ List Token ⇝ Program`. This file
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

## …and the same stage at the vernacular level

`Typing.lean` folds all four of those through a whole file. `programStage` is the resulting
morphism `Program ⇝ elaborated Program`, and composing it after `Language.pipeline` gives

```
List Char ⇝ List Token ⇝ Program ⇝ elaborated Program
```

— the entire front end, type checking included, as one `Abs` morphism, derived from a filled-in
`ElaboratableLanguage` and nothing else.
-/

namespace LambdaLab.Language

open LambdaLab.Abstraction

/-- The **elaborable** pairs at `Γ`: those some surface form means. This, not all of `Tm × Ty`,
is what elaboration abstracts *onto* — `Abstraction.default` is total over the abstract type, so
taking `Tm × Ty` there would demand a surface form for ill-typed pairs too. -/
def Elaborable (L : ElaboratableLanguage) (Γ : Context (Var L.toLanguage) L.Ty) : Type :=
  { p : L.Tm × L.Ty // ∃ t τ, L.Elaborates Γ t p.1 τ p.2 }

/-- **Elaboration as an `Abs` morphism**, at a fixed context. Concrete is what the author wrote —
a term and the type they declared for it; abstract is what it means; the annotation records the
surface forms that mean it. -/
def elabStage (L : ElaboratableLanguage) (Γ : Context (Var L.toLanguage) L.Ty) :
    Abstraction (L.Tm × L.Ty) (Elaborable L Γ)
      (fun p => { s : L.Tm × L.Ty // L.Elaborates Γ s.1 p.val.1 s.2 p.val.2 }) where
  abstract s := (L.elaborate Γ s.1 s.2).map fun q => ⟨q.val, s.1, s.2, q.property⟩
  realize ann := ann.val
  default {p} := ⟨L.quote p.val.1 p.val.2, L.quote_elaborates p.property⟩
  abstract_realize p ann := by
    show ((L.elaborate Γ ann.val.1 ann.val.2).map _) = some p
    have hsome := L.elaborate_complete ann.property
    cases hq : L.elaborate Γ ann.val.1 ann.val.2 with
    | none => rw [hq] at hsome; simp at hsome
    | some q =>
        obtain ⟨heq1, heq2⟩ := L.elaborates_unique q.property ann.property
        simp only [Option.map_some, Option.some.injEq]
        exact Subtype.ext (Prod.ext heq1 heq2)

/-! ## The vernacular level -/

/-- The **elaborable programs**: those some source file means. Same reason as `Elaborable` — an
arbitrary `Program` of already-elaborated commands need not be anything the elaborator produces,
and `default` would have no surface form to offer for it. -/
def ElaborableProgram (L : ElaboratableLanguage) : Type :=
  { p' : Program L.toLanguage // ∃ p, Program.Elaborates L p p' }

/-- **Elaborating a file as an `Abs` morphism**: the written program to its meaning, annotated by
the programs that mean it. Every field is the corresponding lift from `Typing.lean`. -/
def programStage (L : ElaboratableLanguage) :
    Abstraction (Program L.toLanguage) (ElaborableProgram L)
      (fun p' => { p : Program L.toLanguage // Program.Elaborates L p p'.val }) where
  abstract p := (Program.elaborate L p).map fun q => ⟨q.val, p, q.property⟩
  realize ann := ann.val
  default {p'} := ⟨Program.quote L p'.val, p'.property.elim fun _ h => Program.quote_elaborates h⟩
  abstract_realize p' ann := by
    show ((Program.elaborate L ann.val).map _) = some p'
    have hsome := Program.elaborate_complete ann.property
    cases hq : Program.elaborate L ann.val with
    | none => rw [hq] at hsome; simp at hsome
    | some q =>
        simp only [Option.map_some, Option.some.injEq]
        exact Subtype.ext (Program.elaborates_unique q.property ann.property)

/-- **The whole front end**: characters to an elaborated program, in `Abs`. Parsing and
elaboration are one morphism, so the round-trip law covers both — `realize` of any annotation
re-parses *and* re-elaborates to exactly the value it indexes. -/
def ElaboratableLanguage.pipeline (L : ElaboratableLanguage) :
    Abstraction (List Char) (ElaborableProgram L)
      (fun p' => Σ ann : { p : Program L.toLanguage // Program.Elaborates L p p'.val },
        Σ a : Program.Ann L.toLanguage ann.val, Gaps isSep (L.parser.print a)) :=
  L.toLanguage.pipeline.comp (programStage L)

/-- Parse *and* elaborate a source file. -/
def ElaboratableLanguage.elaborateFile (L : ElaboratableLanguage) (s : String) :
    Option (ElaborableProgram L) :=
  L.pipeline.abstract s.toList

/-- Render an elaborated program canonically — quoted back to surface form, then printed. -/
def ElaboratableLanguage.renderElaborated (L : ElaboratableLanguage) (p' : ElaborableProgram L) :
    String :=
  String.ofList (L.pipeline.realize (L.pipeline.default (a := p')))

end LambdaLab.Language
