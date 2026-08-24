import LambdaLab.TypeSystem.Named.Basic
import LambdaLab.NEList

namespace LambdaLab.TypeSystem.Named.Vernacular

/-- A single declaration: `def x : τ := t`.

The name is drawn from whatever atoms the surrounding layer uses for *term* variables, not
from a vernacular notion of its own. So `def f : T := e` puts `f` in scope for what follows with
no injection between two kinds of name — and a front end whose name type excludes its keywords
(`Pipeline.Var`) gets, for free, that a command spelling a keyword is unrepresentable. -/
inductive Command (N Tm Ty : Type) where
| decl : N → Ty → Tm → Command N Tm Ty

/-- A program is a **non-empty** run of commands.

Why not `List (Command …)`: a one-or-more parser never *parses* an empty list, so an empty program
has no printed form to parse back — it would falsify a front end's round-trip law. `NEList` is
also `Command × List Command`, which is what lets substitution reach a whole program through the
pair and list instances rather than through an instance of its own. -/
abbrev Program (N Tm Ty : Type) := NEList (Command N Tm Ty)

namespace Command

variable {N Tm Ty : Type}

def name : Command N Tm Ty → N  | .decl n _ _ => n
def ty   : Command N Tm Ty → Ty | .decl _ τ _ => τ
def tm   : Command N Tm Ty → Tm | .decl _ _ t => t

end Command

/-! ## Substituting through a program

One instance, for `Command`. `Program` is `NEList (Command …)`, which is `Command × List Command`,
and `Substitution/Basic.lean` already has the pair and list instances — so applying a substitution
to a whole program, and the laws about doing so, come for free the moment a single declaration
knows how.

A declaration's *name* is untouched: substitution replaces metavariables, and a binder name is not
one. Support therefore ranges over the declared type and the body only. -/

variable {N Tm Ty : Type}

instance instHasSubstCommand [HasSubst Nat Tm Ty] [HasSubst Nat Ty Ty] :
    HasSubst Nat (Command N Tm Ty) Ty where
  pSubst c σ := match c with
    | .decl x τ t => .decl x (HasSubst.pSubst τ σ) (HasSubst.pSubst t σ)
  isFree c n := match c with
    | .decl _ τ t => HasVars.isFree τ n ∨ HasVars.isFree t n
  supp c := match c with
    | .decl _ τ t => HasVars.supp (A := Nat) τ ++ HasVars.supp (A := Nat) t
  mem_supp_iff_isFree := by
    rintro ⟨x, τ, t⟩ n
    simp only [List.mem_append, HasVars.mem_supp_iff_isFree]

@[simp] theorem Command.pSubst_decl [HasSubst Nat Tm Ty] [HasSubst Nat Ty Ty]
    (x : N) (τ : Ty) (t : Tm) (σ : Subst Nat Ty) :
    HasSubst.pSubst (Command.decl x τ t) σ
      = Command.decl x (HasSubst.pSubst τ σ) (HasSubst.pSubst t σ) := rfl

/-- A ground declaration is untouched by substitution. Together with the pair and list instances
of `Nominal/Unification/Subst.lean` this reaches a whole `Program`, which is what makes an elaborated
file a fixed point of its own elaborator. -/
instance instGroundStableCommand [HasSubst Nat Tm Ty] [HasSubst Nat Ty Ty]
    [GroundStable Nat Tm Ty] [GroundStable Nat Ty Ty] : GroundStable Nat (Command N Tm Ty) Ty where
  pSubst_ground {c} σ h := by
    obtain ⟨x, τ, t⟩ := c
    show Command.decl x _ _ = Command.decl x _ _
    rw [GroundStable.pSubst_ground σ (fun n hn => h n (Or.inl hn)),
        GroundStable.pSubst_ground σ (fun n hn => h n (Or.inr hn))]

instance instLawfulCompCommand [HasSubst Nat Tm Ty] [HasSubst Nat Ty Ty]
    [LawfulComp Nat Tm Ty] [LawfulComp Nat Ty Ty] : LawfulComp Nat (Command N Tm Ty) Ty where
  pSubst_comp c σ τ := by
    obtain ⟨x, ρ, t⟩ := c
    show Command.decl x _ _ = Command.decl x _ _
    rw [LawfulComp.pSubst_comp ρ σ τ, LawfulComp.pSubst_comp t σ τ]

/-- A declaration's atoms are its type's and its body's together, so an atom set the declaration
sits inside is one both sit inside. With the pair and list instances this reaches a whole
`Program`, which is what lets `elabProgram` prune its answer. -/
instance instLawfulRestrictCommand [HasSubst Nat Tm Ty] [HasSubst Nat Ty Ty]
    [LawfulRestrict Nat Tm Ty] [LawfulRestrict Nat Ty Ty] : LawfulRestrict Nat (Command N Tm Ty) Ty where
  pSubst_restrictTo c σ s h := by
    obtain ⟨x, τ, t⟩ := c
    show Command.decl x _ _ = Command.decl x _ _
    rw [LawfulRestrict.pSubst_restrictTo τ σ s (fun a ha => h a (Or.inl ha)),
        LawfulRestrict.pSubst_restrictTo t σ s (fun a ha => h a (Or.inr ha))]

end LambdaLab.TypeSystem.Named.Vernacular
