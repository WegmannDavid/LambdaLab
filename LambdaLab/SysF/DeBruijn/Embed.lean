import LambdaLab.Stlc.DeBruijn.TypeSystem
import LambdaLab.SysF.DeBruijn.TypeSystem
import LambdaLab.TypeSystem.DeBruijn.Category

/-!
# STLC embeds in System F — the morphism the subobject will be

The inclusion `DBSys` was built for: STLC's terms and types map structurally into System F's,
typing carries over rule for rule, and every STLC step is the same step over there. The one
non-structural clause is the whole design: **STLC's `Ty.mvar n` becomes F's `Ty.var n`** — the
opaque atoms of the simply-typed judgement are the free type variables of the polymorphic one,
which behave identically (equal to themselves, no rules) because F's judgement deliberately
does not check type-variable scoping. Injectivity is by construction; when subobjects arrive,
this morphism is the mono exhibiting STLC as a fragment of System F.

The commutation lemmas earn the step transport: an embedded term never contains `tlam` or
`tapp`, so `Term.subst`'s F-side recursion only ever visits its STLC-shaped clauses, and the
embedding slides through shift and substitution by plain induction.

Mathlib enters through the category — so, per the recorded hazard, the reduction arrows are
spelled `Step`/`RTC` here rather than `⟶`.
-/

namespace LambdaLab.SysF.DeBruijn

/-- Types embed; the `mvar ↦ var` clause is the header's story. -/
def embedTy : Stlc.DeBruijn.Ty → Ty
  | .base      => .base
  | .arrow a b => .arrow (embedTy a) (embedTy b)
  | .mvar n    => .var n

/-- Terms embed structurally — nothing to invent, STLC's constructors are a prefix of F's. -/
def embedTm : Stlc.DeBruijn.Term → Term
  | .var n     => .var n
  | .lam τ e   => .lam (embedTy τ) (embedTm e)
  | .app e₁ e₂ => .app (embedTm e₁) (embedTm e₂)

/-- The embedding slides through term-variable shifting. -/
theorem embedTm_shift : ∀ (e : Stlc.DeBruijn.Term) (c : Nat),
    embedTm (e.shift c) = (embedTm e).shift c
  | .var n, c => by
      simp only [Stlc.DeBruijn.Term.shift, Term.shift, embedTm]
      split <;> simp [embedTm]
  | .lam τ e, c => by
      simp only [Stlc.DeBruijn.Term.shift, Term.shift, embedTm, embedTm_shift e (c + 1)]
  | .app e₁ e₂, c => by
      simp only [Stlc.DeBruijn.Term.shift, Term.shift, embedTm,
        embedTm_shift e₁ c, embedTm_shift e₂ c]

/-- …and through substitution: the F-side recursion only ever meets STLC-shaped clauses. -/
theorem embedTm_subst : ∀ (e : Stlc.DeBruijn.Term) (n : Nat) (v : Stlc.DeBruijn.Term),
    embedTm (e.subst n v) = (embedTm e).subst n (embedTm v)
  | .var m, n, v => by
      simp only [Stlc.DeBruijn.Term.subst, Term.subst, embedTm]
      split
      · rfl
      · split <;> simp [embedTm]
  | .lam τ e, n, v => by
      simp only [Stlc.DeBruijn.Term.subst, Term.subst, embedTm,
        embedTm_subst e (n + 1) (v.shift 0), embedTm_shift v 0]
  | .app e₁ e₂, n, v => by
      simp only [Stlc.DeBruijn.Term.subst, Term.subst, embedTm,
        embedTm_subst e₁ n v, embedTm_subst e₂ n v]

/-- Lookup embeds positionally. -/
theorem embed_lookup {Γ : Stlc.DeBruijn.Ctx} {n : Nat} {τ : Stlc.DeBruijn.Ty}
    (h : Stlc.DeBruijn.Lookup Γ n τ) :
    Lookup (Γ.map embedTy) n (embedTy τ) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

/-- **Typing embeds, rule for rule** — the STLC derivation replayed with F's constructors, the
`mvar ↦ var` clause never even visible because the judgement treats both as atoms. -/
theorem embed_hasType {Γ : Stlc.DeBruijn.Ctx} {e : Stlc.DeBruijn.Term}
    {τ : Stlc.DeBruijn.Ty} (h : Stlc.DeBruijn.HasType Γ e τ) :
    HasType (Γ.map embedTy) (embedTm e) (embedTy τ) := by
  induction h with
  | var hl => exact .var (embed_lookup hl)
  | lam _ ih => exact .lam ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂

/-- **Steps embed as steps** — β is β, through the substitution commutation. -/
theorem embed_step {e e' : Stlc.DeBruijn.Term} (s : Stlc.DeBruijn.Step e e') :
    Step (embedTm e) (embedTm e') := by
  induction s with
  | @beta τ b v =>
      show Step (.app (.lam (embedTy τ) (embedTm b)) (embedTm v)) (embedTm (b.subst 0 v))
      rw [embedTm_subst]
      exact .beta
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih

/-- STLC, as an object of `DBSys`. -/
def stlcSys : TypeSystem.DeBruijn.Sys :=
  { Tm := Stlc.DeBruijn.Term, Ty := Stlc.DeBruijn.Ty }

/-- System F, as an object of `DBSys`. -/
def sysfSys : TypeSystem.DeBruijn.Sys :=
  { Tm := Term, Ty := Ty }

/-- **The inclusion** — typing on the nose, each step a single step (`RTC.single` is the lax
form's witness). Injective in both components by construction; when subobjects arrive in
`DBSys`, this is the mono exhibiting STLC as a fragment of System F. -/
def stlcEmbed : TypeSystem.DeBruijn.Hom stlcSys sysfSys where
  mapTm := embedTm
  mapTy := embedTy
  mapTyping h := embed_hasType h
  mapStep s := RTC.single (embed_step s)

end LambdaLab.SysF.DeBruijn
