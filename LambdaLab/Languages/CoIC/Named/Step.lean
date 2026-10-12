import LambdaLab.Languages.CoIC.Named.Translation
import LambdaLab.Languages.CoIC.DeBruijn.Eval

/-!
# CoIC, named — reduction

Full β and ι on named terms, anywhere — domains and annotations included — β by capture-avoiding
substitution, `(λ x : A . b) u ⟶ b[x := u]`, and ι as in `DeBruijn/Reduction.lean`.

**It is de Bruijn reduction, read through the translation, in both directions**:

* every named step is exactly one de Bruijn step of the translation (`Step.toDB`) — because
  substitution commutes with the translation (`Tm.toDB_inst`);
* every de Bruijn step of a translation comes from a named step (`Step.reflect`) — the redexes of
  `t.toDB ns` sit exactly where the redexes of `t` do.

So a named term is normal exactly when its translation is (`normal_iff_toDB`), and strong
normalization transfers back along the translation (`sn_of_toDB`).
-/

namespace LambdaLab.Languages.CoIC.Named

open LambdaLab.Nominal (Atom)
open LambdaLab (SN)

/-- **One step of full β-reduction**, named. -/
inductive Step {N : Type} [Atom N] : Tm N → Tm N → Prop
  | beta {x : N} {A b u : Tm N} : Step (.app (.lam x A b) u) (b.inst x u)
  | appL {t t' u : Tm N} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm N} : Step u u' → Step (.app t u) (.app t u')
  | lamA {x : N} {A A' t : Tm N} : Step A A' → Step (.lam x A t) (.lam x A' t)
  | lamB {x : N} {A t t' : Tm N} : Step t t' → Step (.lam x A t) (.lam x A t')
  | piA {x : N} {A A' B : Tm N} : Step A A' → Step (.pi x A B) (.pi x A' B)
  | piB {x : N} {A B B' : Tm N} : Step B B' → Step (.pi x A B) (.pi x A B')
  | iota {i k : Nat} {mask : List Bool} {C bs as : Tm N} : bs.isList = true → as.isList = true →
      Step (.elim i C bs (.ctor i k mask as)) (Tm.iotaRhs i C bs k mask as)
  | ctorA {i k : Nat} {mask : List Bool} {as as' : Tm N} : Step as as' →
      Step (.ctor i k mask as) (.ctor i k mask as')
  | elimC {i : Nat} {C C' bs t : Tm N} : Step C C' → Step (.elim i C bs t) (.elim i C' bs t)
  | elimB {i : Nat} {C bs bs' t : Tm N} : Step bs bs' → Step (.elim i C bs t) (.elim i C bs' t)
  | elimT {i : Nat} {C bs t t' : Tm N} : Step t t' → Step (.elim i C bs t) (.elim i C bs t')
  | consH {a a' l : Tm N} : Step a a' → Step (.tcons a l) (.tcons a' l)
  | consT {a l l' : Tm N} : Step l l' → Step (.tcons a l) (.tcons a l')

variable {N : Type} [Atom N]

/-- **Simulation**: a named step is one de Bruijn step of the translation, against any binders. -/
theorem Step.toDB {t t' : Tm N} (h : Step t t') :
    ∀ ns : List N, DeBruijn.Step (t.toDB ns) (t'.toDB ns) := by
  induction h with
  | beta => intro ns; rw [Tm.toDB_inst]; exact .beta
  | appL _ ih => intro ns; exact .appL (ih ns)
  | appR _ ih => intro ns; exact .appR (ih ns)
  | lamA _ ih => intro ns; exact .lamA (ih ns)
  | lamB _ ih => intro ns; exact .lamB (ih _)
  | piA _ ih => intro ns; exact .piA (ih ns)
  | piB _ ih => intro ns; exact .piB (ih _)
  | iota hb ha =>
      intro ns
      rw [Tm.iotaRhs_toDB]
      exact .iota (by rw [Tm.isList_toDB]; exact hb) (by rw [Tm.isList_toDB]; exact ha)
  | ctorA _ ih => intro ns; exact .ctorA (ih ns)
  | elimC _ ih => intro ns; exact .elimC (ih ns)
  | elimB _ ih => intro ns; exact .elimB (ih ns)
  | elimT _ ih => intro ns; exact .elimT (ih ns)
  | consH _ ih => intro ns; exact .consH (ih ns)
  | consT _ ih => intro ns; exact .consT (ih ns)

/-- **Reflection**: a de Bruijn step of a translation is the translation of a named step. -/
theorem Step.reflect : ∀ (t : Tm N) (ns : List N) (w : DeBruijn.Tm),
    DeBruijn.Step (t.toDB ns) w → ∃ t', Step t t' ∧ t'.toDB ns = w
  | .var _, _, _, h => absurd h DeBruijn.Step.var_inv
  | .sort _, _, _, h => absurd h DeBruijn.Step.sort_inv
  | .pi x A B, ns, _, h => by
      simp only [Tm.toDB] at h
      cases h with
      | piA hs =>
          obtain ⟨A', hA', e⟩ := Step.reflect A ns _ hs
          exact ⟨.pi x A' B, .piA hA', by simp only [Tm.toDB, e]⟩
      | piB hs =>
          obtain ⟨B', hB', e⟩ := Step.reflect B (x :: ns) _ hs
          exact ⟨.pi x A B', .piB hB', by simp only [Tm.toDB, e]⟩
  | .lam x A b, ns, _, h => by
      simp only [Tm.toDB] at h
      cases h with
      | lamA hs =>
          obtain ⟨A', hA', e⟩ := Step.reflect A ns _ hs
          exact ⟨.lam x A' b, .lamA hA', by simp only [Tm.toDB, e]⟩
      | lamB hs =>
          obtain ⟨b', hb', e⟩ := Step.reflect b (x :: ns) _ hs
          exact ⟨.lam x A b', .lamB hb', by simp only [Tm.toDB, e]⟩
  | .app t u, ns, w, h => by
      simp only [Tm.toDB] at h
      generalize ht : t.toDB ns = t₀ at h
      cases h with
      | beta =>
          cases t with
          | lam x A b =>
              simp only [Tm.toDB, DeBruijn.Tm.lam.injEq] at ht
              obtain ⟨_, rfl⟩ := ht
              exact ⟨b.inst x u, .beta, Tm.toDB_inst b x u ns⟩
          | _ => simp [Tm.toDB] at ht
      | appL hs =>
          subst ht
          obtain ⟨t', ht', e⟩ := Step.reflect t ns _ hs
          exact ⟨.app t' u, .appL ht', by simp only [Tm.toDB, e]⟩
      | appR hs =>
          subst ht
          obtain ⟨u', hu', e⟩ := Step.reflect u ns _ hs
          exact ⟨.app t u', .appR hu', by simp only [Tm.toDB, e]⟩
  | .ind _, _, _, h => absurd h DeBruijn.Step.ind_inv
  | .tnil, _, _, h => absurd h DeBruijn.Step.tnil_inv
  | .ctor i k m as, ns, _, h => by
      simp only [Tm.toDB] at h
      cases h with
      | ctorA hs =>
          obtain ⟨as', has', e⟩ := Step.reflect as ns _ hs
          exact ⟨.ctor i k m as', .ctorA has', by simp only [Tm.toDB, e]⟩
  | .tcons a l, ns, _, h => by
      simp only [Tm.toDB] at h
      cases h with
      | consH hs =>
          obtain ⟨a', ha', e⟩ := Step.reflect a ns _ hs
          exact ⟨.tcons a' l, .consH ha', by simp only [Tm.toDB, e]⟩
      | consT hs =>
          obtain ⟨l', hl', e⟩ := Step.reflect l ns _ hs
          exact ⟨.tcons a l', .consT hl', by simp only [Tm.toDB, e]⟩
  | .elim i C bs t, ns, w, h => by
      simp only [Tm.toDB] at h
      generalize ht : t.toDB ns = t₀ at h
      cases h with
      | iota hb ha =>
          cases t with
          | ctor i' k m as =>
              simp only [Tm.toDB, DeBruijn.Tm.ctor.injEq] at ht
              obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
              refine ⟨Tm.iotaRhs _ C bs k m as, .iota ?_ ?_, Tm.iotaRhs_toDB _ C bs k m as ns⟩
              · rw [← Tm.isList_toDB bs ns]; exact hb
              · rw [← Tm.isList_toDB as ns]; exact ha
          | _ => simp [Tm.toDB] at ht
      | elimC hs =>
          subst ht
          obtain ⟨C', hC', e⟩ := Step.reflect C ns _ hs
          exact ⟨.elim i C' bs t, .elimC hC', by simp only [Tm.toDB, e]⟩
      | elimB hs =>
          subst ht
          obtain ⟨bs', hbs', e⟩ := Step.reflect bs ns _ hs
          exact ⟨.elim i C bs' t, .elimB hbs', by simp only [Tm.toDB, e]⟩
      | elimT hs =>
          subst ht
          obtain ⟨t', ht', e⟩ := Step.reflect t ns _ hs
          exact ⟨.elim i C bs t', .elimT ht', by simp only [Tm.toDB, e]⟩

/-- A named term is **normal**: it has no reduct. -/
def Tm.Normal (t : Tm N) : Prop := ∀ w, ¬ Step t w

/-- **A named term is normal exactly when its translation is**, against any binders. -/
theorem normal_iff_toDB (t : Tm N) (ns : List N) : t.Normal ↔ (t.toDB ns).Normal := by
  constructor
  · intro h w hw
    obtain ⟨t', ht', _⟩ := Step.reflect t ns w hw
    exact h t' ht'
  · intro h t' ht'
    exact h _ (ht'.toDB ns)

/-- **Strong normalization transfers back** along the translation: an infinite named reduction
would translate into an infinite de Bruijn one. -/
theorem sn_of_toDB {t : Tm N} {ns : List N} (h : SN DeBruijn.Step (t.toDB ns)) : SN Step t := by
  generalize hx : t.toDB ns = x at h
  induction h generalizing t with
  | intro _ ih =>
      subst hx
      exact .intro fun t' hs => ih _ (hs.toDB ns) rfl

end LambdaLab.Languages.CoIC.Named
