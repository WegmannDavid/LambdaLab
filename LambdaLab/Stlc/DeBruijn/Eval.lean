import LambdaLab.Stlc.DeBruijn.Basic
import LambdaLab.Stlc.DeBruijn.Step
import LambdaLab.Stlc.DeBruijn.Reducibility

/-!
# Total normalizer

`Term.eval e h` returns the normal form of `e`, given a strong-normalization
proof. `HasType.eval ht` is the convenience wrapper that supplies the SN
proof via `HasType.sn`.

The evaluator is `noncomputable`: it picks a reduct using classical choice
and recurses via well-founded recursion on the `SN` derivation.
-/

namespace LambdaLab.Stlc.DeBruijn

/-- Convert an `SN` derivation to the corresponding `Acc` derivation. -/
theorem SN.toAcc : ∀ {e : Term}, SN e → Acc (fun x y => y ⟶ x) e := by
  intro e h
  induction h with
  | intro _ ih => exact Acc.intro _ (fun y hy => ih y hy)

open Classical in
/-- Total evaluator: classically picks a reduct of `e` and recurses,
returning `e` itself when no reduct exists. -/
noncomputable def Term.eval (e : Term) (h : SN e) : Term :=
  Acc.recOn (motive := fun e _ => Term) h.toAcc fun e _ ih =>
    if h_red : ∃ e' : Term, e ⟶ e' then
      ih (Classical.choose h_red) (Classical.choose_spec h_red)
    else e

/-- Any well-typed term has a normal form. -/
noncomputable def HasType.eval {Γ : Ctx} {e : Term} {τ : Ty}
    (ht : HasType Γ e τ) : Term :=
  Term.eval e (HasType.sn ht)

end LambdaLab.Stlc.DeBruijn
