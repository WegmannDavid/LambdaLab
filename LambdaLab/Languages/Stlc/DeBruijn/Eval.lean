import LambdaLab.Stlc.DeBruijn.Basic
import LambdaLab.Stlc.DeBruijn.Step
import LambdaLab.Stlc.DeBruijn.Reducibility

/-!
# Total normalizer (de Bruijn variant)

`Term.eval e h` returns the normal form of `e`, given a strong-normalization
proof. `HasType.eval ht` is the convenience wrapper that supplies the SN
proof via `HasType.sn`.

The recursion is on the term: `findReductStep` picks a leftmost-outermost
redex (structural recursion on `Term`); the outer loop iterates that
until the term is in normal form. Termination of the loop is certified
by `SN`, packaged into a `WellFoundedRelation` on `SNTerm`.
-/

namespace LambdaLab.Stlc.DeBruijn

/-- Computable redex picker: leftmost-outermost. -/
def Term.findReductStep : (e : Term) → Option ((e' : Term) ×' Step e e')
  | .var _                  => none
  | .lam τ body             =>
      match body.findReductStep with
      | some ⟨body', s⟩ => some ⟨.lam τ body', Step.lam s⟩
      | none            => none
  | .app (.lam _ body) v    =>
      some ⟨body.subst 0 v, Step.beta⟩
  | .app f a                =>
      match f.findReductStep with
      | some ⟨f', s⟩ => some ⟨.app f' a, Step.appL s⟩
      | none =>
          match a.findReductStep with
          | some ⟨a', s⟩ => some ⟨.app f a', Step.appR s⟩
          | none         => none

abbrev SNTerm := { e : Term // SN e }

instance : WellFoundedRelation SNTerm where
  rel := fun a b => Step b.val a.val
  wf := ⟨fun ⟨_, h⟩ => by
    induction h with
    | intro _ ih =>
        constructor
        intro ⟨e', _⟩ hs
        exact ih e' hs⟩

/-- Total evaluator: returns the normal form of `e` given an `SN` proof. -/
def Term.eval (e : Term) (h : SN e) : Term :=
  match e.findReductStep with
  | none         => e
  | some ⟨e', s⟩ => Term.eval e' (h.unfold s)
termination_by (⟨e, h⟩ : SNTerm)

/-- Any well-typed term has a normal form. -/
def HasType.eval {Γ : Ctx} {e : Term} {τ : Ty} (ht : HasType Γ e τ) : Term :=
  Term.eval e (HasType.sn ht)

end LambdaLab.Stlc.DeBruijn
