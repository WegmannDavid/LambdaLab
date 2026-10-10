import LambdaLab.Languages.SystemF.Named.Translation
import LambdaLab.Languages.SystemF.DeBruijn.Eval

/-!
# System F, named — reduction

Full β on named terms, under binders included, by capture-avoiding substitution:

    (λ x : A . b) u  ⟶  b[x := u]          (Λ α . b) [B]  ⟶  b[α := B]

**It is de Bruijn reduction, read through the translation, in both directions**:

* every named step is exactly one de Bruijn step of the translation (`Step.toDB`) — because the
  substitutions commute with the translation (`Tm.toDB_inst`, `Tm.toDB_tinst`);
* every de Bruijn step of a translation comes from a named step (`Step.reflect`) — the redexes of
  `t.toDB Θ Γ` sit exactly where the redexes of `t` do.

So a named term is normal exactly when its translation is (`normal_iff_toDB`), and strong
normalization transfers back along the translation (`sn_of_toDB`).
-/

namespace LambdaLab.Languages.SystemF.Named

open LambdaLab.Nominal (Atom)

/-- **One step of full β-reduction**, named. -/
inductive Step {N : Type} [Atom N] : Tm N → Tm N → Prop
  | beta {x : N} {A : Ty N} {b u : Tm N} : Step (.app (.lam x A b) u) (b.inst x u)
  | tbeta {α : N} {b : Tm N} {B : Ty N} : Step (.tapp (.tlam α b) B) (b.tinst α B)
  | lam {x : N} {A : Ty N} {b b' : Tm N} : Step b b' → Step (.lam x A b) (.lam x A b')
  | appL {t t' u : Tm N} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm N} : Step u u' → Step (.app t u) (.app t u')
  | tlam {α : N} {b b' : Tm N} : Step b b' → Step (.tlam α b) (.tlam α b')
  | tappL {t t' : Tm N} {B : Ty N} : Step t t' → Step (.tapp t B) (.tapp t' B)

variable {N : Type} [Atom N]

/-- **Simulation**: a named step is one de Bruijn step of the translation, against any binders. -/
theorem Step.toDB {t t' : Tm N} (h : Step t t') :
    ∀ Θ Γ : List N, DeBruijn.Step (t.toDB Θ Γ) (t'.toDB Θ Γ) := by
  induction h with
  | beta => intro Θ Γ; rw [Tm.toDB_inst]; exact .beta
  | tbeta => intro Θ Γ; rw [Tm.toDB_tinst]; exact .tbeta
  | lam _ ih => intro Θ Γ; exact .lam (ih _ _)
  | appL _ ih => intro Θ Γ; exact .appL (ih Θ Γ)
  | appR _ ih => intro Θ Γ; exact .appR (ih Θ Γ)
  | tlam _ ih => intro Θ Γ; exact .tlam (ih _ _)
  | tappL _ ih => intro Θ Γ; exact .tappL (ih Θ Γ)

/-- **Reflection**: a de Bruijn step of a translation is the translation of a named step. -/
theorem Step.reflect : ∀ (t : Tm N) (Θ Γ : List N) (w : DeBruijn.Tm),
    DeBruijn.Step (t.toDB Θ Γ) w → ∃ t', Step t t' ∧ t'.toDB Θ Γ = w
  | .var _, _, _, _, h => absurd h DeBruijn.Step.var_inv
  | .lam x A b, Θ, Γ, _, h => by
      obtain ⟨w', hw', rfl⟩ := DeBruijn.Step.lam_inv h
      obtain ⟨b', hb', e⟩ := Step.reflect b Θ (x :: Γ) w' hw'
      exact ⟨.lam x A b', .lam hb', by simp only [Tm.toDB, e]⟩
  | .app t u, Θ, Γ, w, h => by
      simp only [Tm.toDB] at h
      generalize ht : t.toDB Θ Γ = t₀ at h
      cases h with
      | beta =>
          cases t with
          | lam x A b =>
              simp only [Tm.toDB, DeBruijn.Tm.lam.injEq] at ht
              obtain ⟨_, rfl⟩ := ht
              exact ⟨b.inst x u, .beta, Tm.toDB_inst b x u Θ Γ⟩
          | var => simp [Tm.toDB] at ht
          | app => simp [Tm.toDB] at ht
          | tlam => simp [Tm.toDB] at ht
          | tapp => simp [Tm.toDB] at ht
      | appL hs =>
          subst ht
          obtain ⟨t', ht', e⟩ := Step.reflect t Θ Γ _ hs
          exact ⟨.app t' u, .appL ht', by simp only [Tm.toDB, e]⟩
      | appR hs =>
          subst ht
          obtain ⟨u', hu', e⟩ := Step.reflect u Θ Γ _ hs
          exact ⟨.app t u', .appR hu', by simp only [Tm.toDB, e]⟩
  | .tlam α b, Θ, Γ, _, h => by
      obtain ⟨w', hw', rfl⟩ := DeBruijn.Step.tlam_inv h
      obtain ⟨b', hb', e⟩ := Step.reflect b (α :: Θ) Γ w' hw'
      exact ⟨.tlam α b', .tlam hb', by simp only [Tm.toDB, e]⟩
  | .tapp t B, Θ, Γ, w, h => by
      simp only [Tm.toDB] at h
      generalize ht : t.toDB Θ Γ = t₀ at h
      cases h with
      | tbeta =>
          cases t with
          | tlam α b =>
              simp only [Tm.toDB, DeBruijn.Tm.tlam.injEq] at ht
              subst ht
              exact ⟨b.tinst α B, .tbeta, Tm.toDB_tinst b α B Θ Γ⟩
          | var => simp [Tm.toDB] at ht
          | lam => simp [Tm.toDB] at ht
          | app => simp [Tm.toDB] at ht
          | tapp => simp [Tm.toDB] at ht
      | tappL hs =>
          subst ht
          obtain ⟨t', ht', e⟩ := Step.reflect t Θ Γ _ hs
          exact ⟨.tapp t' B, .tappL ht', by simp only [Tm.toDB, e]⟩

/-- A named term is **normal**: it has no reduct. -/
def Tm.Normal (t : Tm N) : Prop := ∀ w, ¬ Step t w

/-- **A named term is normal exactly when its translation is**, against any binders. -/
theorem normal_iff_toDB (t : Tm N) (Θ Γ : List N) : t.Normal ↔ (t.toDB Θ Γ).Normal := by
  constructor
  · intro h w hw
    obtain ⟨t', ht', _⟩ := Step.reflect t Θ Γ w hw
    exact h t' ht'
  · intro h t' ht'
    exact h _ (ht'.toDB Θ Γ)

/-- **Strong normalization transfers back** along the translation: an infinite named reduction
would translate into an infinite de Bruijn one. -/
theorem sn_of_toDB {t : Tm N} {Θ Γ : List N} (h : SN DeBruijn.Step (t.toDB Θ Γ)) : SN Step t := by
  generalize hx : t.toDB Θ Γ = x at h
  induction h generalizing t with
  | intro _ ih =>
      subst hx
      exact .intro fun t' hs => ih _ (hs.toDB Θ Γ) rfl

end LambdaLab.Languages.SystemF.Named
