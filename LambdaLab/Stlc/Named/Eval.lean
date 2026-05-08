import LambdaLab.Stlc.Named.Normalization

/-!
# Total normalizer (named variant)

`Term.eval e h` returns the normal form of `e`, given a strong-normalization
proof. `HasType.eval ht` is the convenience wrapper that supplies the SN
proof via `HasType.sn`.

The recursion is on the term: `findReductStep` picks a leftmost-outermost
redex (structural recursion on `Term`); the outer loop iterates that
until the term is in normal form. Termination of the loop is certified
by `SN`, packaged into a `WellFoundedRelation` on `SNTerm` so Lean
compiles via `WellFounded.fix`.
-/

namespace LambdaLab.Stlc.Named

/-- Computable redex picker: leftmost-outermost. Returns `some ⟨e', s⟩`
where `s : Step e e'` if `e` has any redex; `none` if `e` is in
β-normal form. -/
def Term.findReductStep : (e : Term) → Option ((e' : Term) ×' Step e e')
  | .var _                  => none
  | .lam x τ body           =>
      match body.findReductStep with
      | some ⟨body', s⟩ => some ⟨.lam x τ body', Step.lam s⟩
      | none            => none
  | .app (.lam x _ body) v  =>
      some ⟨body.subst x v, Step.beta⟩
  | .app f a                =>
      match f.findReductStep with
      | some ⟨f', s⟩ => some ⟨.app f' a, Step.appL s⟩
      | none =>
          match a.findReductStep with
          | some ⟨a', s⟩ => some ⟨.app f a', Step.appR s⟩
          | none         => none

/-- An SN-witnessed term. The Subtype packages the `SN` proof so we can
attach a `WellFoundedRelation` whose underlying relation is `Step` on
the term components. -/
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

/-- Any well-typed term has a normal form (given the bridge
preconditions: ground context and ground annotations). -/
def HasType.eval {Γ : Ctx} {e : Term} {τ : Ty}
    (hΓ : Γ.Ground) (hag : e.AnnotsGround) (ht : HasType Γ e τ) : Term :=
  Term.eval e (HasType.sn hΓ hag ht)

end LambdaLab.Stlc.Named
