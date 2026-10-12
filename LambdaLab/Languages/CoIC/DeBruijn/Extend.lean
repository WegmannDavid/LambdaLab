import LambdaLab.Languages.CoIC.DeBruijn.Scope

/-!
# CoIC — growing the signature

A program declares its inductive types one at a time, so the signature grows at the end. Nothing
already derived notices: a judgement over `sg` holds over `sg ++ sg'` (`HasType.extend`), because
every rule consults the signature only at indices it has already checked are in range.

And a valid signature stays valid when one more inductive is added whose argument types are
types over the old signature, mentioning only the inductives before it (`WfSig.snoc`). A front end
checks exactly that, with the old signature's checker, before declaring the new type.
-/

namespace LambdaLab.Languages.CoIC.DeBruijn

theorem Sig.ctorArgs_append {sg : Sig} (sg' : Sig) {i k : Nat} (hi : i < sg.length) :
    (sg ++ sg').ctorArgs i k = sg.ctorArgs i k := by
  simp only [Sig.ctorArgs, List.getElem?_append_left hi]

theorem Sig.numCtors_append {sg : Sig} (sg' : Sig) {i : Nat} (hi : i < sg.length) :
    (sg ++ sg').numCtors i = sg.numCtors i := by
  simp only [Sig.numCtors, List.getElem?_append_left hi]

theorem Sig.numCtors_lt {sg : Sig} {i m : Nat} (h : sg.numCtors i = some m) : i < sg.length := by
  simp only [Sig.numCtors, Option.map_eq_some_iff] at h
  obtain ⟨I, hI, _⟩ := h
  exact (List.getElem?_eq_some_iff.mp hI).1

theorem Sig.ctorArgs_snoc (sg : Sig) (I : IndSpec) (k : Nat) :
    (sg ++ [I]).ctorArgs sg.length k = I.ctors[k]? := by
  simp [Sig.ctorArgs]

theorem Sig.numCtors_snoc (sg : Sig) (I : IndSpec) :
    (sg ++ [I]).numCtors sg.length = some I.ctors.length := by
  simp [Sig.numCtors]

/-- **A judgement survives a longer signature.** -/
theorem HasType.extend {sg : Sig} (sg' : Sig) {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) :
    HasType (sg ++ sg') Γ t T := by
  induction h with
  | sort => exact .sort
  | var hn => exact .var hn
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ _ ihA iht ihB => exact .lam ihA iht ihB
  | app _ _ iht ihu => exact .app iht ihu
  | conv _ _ hc iht ihB => exact .conv iht ihB hc
  | ind hi => exact .ind (by simp; omega)
  | ctor hc hm hl hlen _ ih =>
      exact .ctor (by rw [Sig.ctorArgs_append _ (Sig.ctorArgs_lt hc)]; exact hc) hm hl hlen ih
  | elim hm _ hl hlen _ _ _ ihC ihb iha iht =>
      have hi := Sig.numCtors_lt hm
      refine .elim (by rw [Sig.numCtors_append _ hi]; exact hm) ihC hl hlen
        (fun k c hc => ihb k c (by rwa [Sig.ctorArgs_append _ hi] at hc))
        (fun k c hc => iha k c (by rwa [Sig.ctorArgs_append _ hi] at hc)) iht

theorem Tm.indsLt_mono : ∀ {t : Tm} {n n' : Nat}, t.indsLt n → n ≤ n' → t.indsLt n'
  | .var _, _, _, _, _ => trivial
  | .sort _, _, _, _, _ => trivial
  | .pi _ _, _, _, ⟨hA, hB⟩, hn => ⟨Tm.indsLt_mono hA hn, Tm.indsLt_mono hB hn⟩
  | .lam _ _, _, _, ⟨hA, ht⟩, hn => ⟨Tm.indsLt_mono hA hn, Tm.indsLt_mono ht hn⟩
  | .app _ _, _, _, ⟨ht, hu⟩, hn => ⟨Tm.indsLt_mono ht hn, Tm.indsLt_mono hu hn⟩
  | .ind _, _, _, h, hn => Nat.lt_of_lt_of_le h hn
  | .ctor _ _ _ _, _, _, ⟨hi, has⟩, hn => ⟨Nat.lt_of_lt_of_le hi hn, Tm.indsLt_mono has hn⟩
  | .elim _ _ _ _, _, _, ⟨hi, hC, hbs, ht⟩, hn =>
      ⟨Nat.lt_of_lt_of_le hi hn, Tm.indsLt_mono hC hn, Tm.indsLt_mono hbs hn,
        Tm.indsLt_mono ht hn⟩
  | .tnil, _, _, _, _ => trivial
  | .tcons _ _, _, _, ⟨ha, hl⟩, hn => ⟨Tm.indsLt_mono ha hn, Tm.indsLt_mono hl hn⟩

/-- Whether every inductive a term names is below `n`. -/
instance Tm.decIndsLt (n : Nat) : (t : Tm) → Decidable (t.indsLt n)
  | .var _ => isTrue trivial
  | .sort _ => isTrue trivial
  | .pi A B =>
      have := Tm.decIndsLt n A; have := Tm.decIndsLt n B
      inferInstanceAs (Decidable (A.indsLt n ∧ B.indsLt n))
  | .lam A t =>
      have := Tm.decIndsLt n A; have := Tm.decIndsLt n t
      inferInstanceAs (Decidable (A.indsLt n ∧ t.indsLt n))
  | .app t u =>
      have := Tm.decIndsLt n t; have := Tm.decIndsLt n u
      inferInstanceAs (Decidable (t.indsLt n ∧ u.indsLt n))
  | .ind i => inferInstanceAs (Decidable (i < n))
  | .ctor i _ _ as =>
      have := Tm.decIndsLt n as
      inferInstanceAs (Decidable (i < n ∧ as.indsLt n))
  | .elim i C bs t =>
      have := Tm.decIndsLt n C; have := Tm.decIndsLt n bs; have := Tm.decIndsLt n t
      inferInstanceAs (Decidable (i < n ∧ C.indsLt n ∧ bs.indsLt n ∧ t.indsLt n))
  | .tnil => isTrue trivial
  | .tcons a l =>
      have := Tm.decIndsLt n a; have := Tm.decIndsLt n l
      inferInstanceAs (Decidable (a.indsLt n ∧ l.indsLt n))

/-- What a front end checks of a new inductive's argument types: types over the old signature,
naming only the inductives already declared. -/
def ArgsOk (sg : Sig) (cs : List CtorSpec) : Prop :=
  ∀ c ∈ cs, ∀ A, some A ∈ c → HasType sg [] A (.sort .star) ∧ A.indsLt sg.length

/-- The new inductive, its argument types closed because they are typed in the empty context. -/
def IndSpec.ofArgsOk {sg : Sig} (cs : List CtorSpec) (h : ArgsOk sg cs) : IndSpec where
  ctors := cs
  closed c hc A hA := by simpa using (h c hc A hA).1.scoped

/-- **A valid signature, extended by one checked inductive, is valid.** -/
theorem WfSig.snoc {sg : Sig} (hsg : WfSig sg) {cs : List CtorSpec} (h : ArgsOk sg cs) :
    WfSig (sg ++ [IndSpec.ofArgsOk cs h]) := by
  intro i k c hc A hA
  by_cases hi : i < sg.length
  · rw [Sig.ctorArgs_append _ hi] at hc
    obtain ⟨hT, hl⟩ := hsg i k c hc A hA
    exact ⟨hT.extend _, hl⟩
  · have hi' := Sig.ctorArgs_lt hc
    simp only [List.length_append, List.length_singleton] at hi'
    have e : i = sg.length := by omega
    subst e
    rw [Sig.ctorArgs_snoc] at hc
    obtain ⟨hT, hl⟩ := h c (List.mem_of_getElem? hc) A hA
    exact ⟨hT.extend _, hl⟩

end LambdaLab.Languages.CoIC.DeBruijn
