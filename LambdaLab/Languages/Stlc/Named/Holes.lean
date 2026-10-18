import LambdaLab.Languages.Stlc.Named.TypeSystem

/-!
# STLC — anonymous metavariables

A type may be written `_`, as in Lean: a metavariable no other position shares, for the elaborator
to solve. In the syntax tree `_` is the metavariable `0`, and a written `?k` is `k + 1`
(`Pipeline.lean`'s parser), so the two never meet.

Before elaboration every `_` is given a number of its own (`fillHoles`): left to right, through the
whole program, starting above every metavariable the program mentions — they are global to the
file, so a number taken from a later declaration's `?k` would capture it. That is a function on
whole programs, not a walk: a walk could not see the declarations after the one it is filling.

It becomes a pipeline stage on its own (`Pipeline/Compose.lean`, `DefLanguage.evalChainVia`),
which asks two things of it, both proved here:

* it is **idempotent** (`fillHoles_idem`): a filled program has no `_` left, and filling a program
  with no `_` changes nothing;
* it leaves **well-typed programs** alone (`fillHoles_of_hasType`): they are ground, so they mention
  no metavariable at all.
-/

namespace LambdaLab.Languages.Stlc.Named

open LambdaLab.Nominal (Atom)
open LambdaLab.TypeSystem.Named.Vernacular (Command Program HasTypeGround)

variable {N : Type}

/-! ## Types -/

/-- Does `_` occur? -/
def Ty.hasHole : Ty → Bool
  | .mvar n => n == 0
  | .base => false
  | .arrow a b => a.hasHole || b.hasHole

/-- The largest metavariable, `0` if none. -/
def Ty.maxMvar : Ty → Nat
  | .mvar n => n
  | .base => 0
  | .arrow a b => max a.maxMvar b.maxMvar

/-- Number the `_`s from `n` on, left to right; the next number. -/
def Ty.fill : Ty → Nat → Ty × Nat
  | .mvar 0, n => (.mvar n, n + 1)
  | .mvar k, n => (.mvar k, n)
  | .base, n => (.base, n)
  | .arrow a b, n => (.arrow (a.fill n).1 (b.fill (a.fill n).2).1, (b.fill (a.fill n).2).2)

theorem Ty.fill_of_noHole : ∀ {τ : Ty}, τ.hasHole = false → ∀ n, τ.fill n = (τ, n)
  | .mvar 0, h, _ => by simp [Ty.hasHole] at h
  | .mvar (k + 1), _, _ => rfl
  | .base, _, _ => rfl
  | .arrow a b, h, n => by
      simp only [Ty.hasHole, Bool.or_eq_false_iff] at h
      simp only [Ty.fill, Ty.fill_of_noHole h.1, Ty.fill_of_noHole h.2]

theorem Ty.fill_spec : ∀ (τ : Ty) {n : Nat}, 0 < n →
    (τ.fill n).1.hasHole = false ∧ n ≤ (τ.fill n).2
  | .mvar 0, n, h => by simp [Ty.fill, Ty.hasHole]; omega
  | .mvar (k + 1), _, _ => by simp [Ty.fill, Ty.hasHole]
  | .base, _, _ => by simp [Ty.fill, Ty.hasHole]
  | .arrow a b, n, h => by
      obtain ⟨ha, hna⟩ := Ty.fill_spec a h
      obtain ⟨hb, hnb⟩ := Ty.fill_spec b (Nat.lt_of_lt_of_le h hna)
      simp only [Ty.fill, Ty.hasHole, ha, hb, Bool.or_false, true_and]
      omega

theorem Ty.hasHole_of_isGround : ∀ {τ : Ty}, τ.isGround = true → τ.hasHole = false
  | .mvar _, h => by simp [Ty.isGround] at h
  | .base, _ => rfl
  | .arrow a b, h => by
      simp only [Ty.isGround, Bool.and_eq_true] at h
      simp [Ty.hasHole, Ty.hasHole_of_isGround h.1, Ty.hasHole_of_isGround h.2]

/-! ## Terms: the `_`s of their annotations -/

def Term.hasHole : Term N → Bool
  | .var _ => false
  | .lam _ τ b => τ.hasHole || b.hasHole
  | .app f a => f.hasHole || a.hasHole

def Term.maxMvar : Term N → Nat
  | .var _ => 0
  | .lam _ τ b => max τ.maxMvar b.maxMvar
  | .app f a => max f.maxMvar a.maxMvar

def Term.fill : Term N → Nat → Term N × Nat
  | .var x, n => (.var x, n)
  | .lam x τ b, n => (.lam x (τ.fill n).1 (b.fill (τ.fill n).2).1, (b.fill (τ.fill n).2).2)
  | .app f a, n => (.app (f.fill n).1 (a.fill (f.fill n).2).1, (a.fill (f.fill n).2).2)

theorem Term.fill_of_noHole : ∀ {t : Term N}, t.hasHole = false → ∀ n, t.fill n = (t, n)
  | .var _, _, _ => rfl
  | .lam x τ b, h, n => by
      simp only [Term.hasHole, Bool.or_eq_false_iff] at h
      simp only [Term.fill, Ty.fill_of_noHole h.1, Term.fill_of_noHole h.2]
  | .app f a, h, n => by
      simp only [Term.hasHole, Bool.or_eq_false_iff] at h
      simp only [Term.fill, Term.fill_of_noHole h.1, Term.fill_of_noHole h.2]

theorem Term.fill_spec : ∀ (t : Term N) {n : Nat}, 0 < n →
    (t.fill n).1.hasHole = false ∧ n ≤ (t.fill n).2
  | .var _, _, _ => by simp [Term.fill, Term.hasHole]
  | .lam x τ b, n, h => by
      obtain ⟨hτ, hn₁⟩ := Ty.fill_spec τ h
      obtain ⟨hb, hn₂⟩ := Term.fill_spec b (Nat.lt_of_lt_of_le h hn₁)
      simp only [Term.fill, Term.hasHole, hτ, hb, Bool.or_false, true_and]
      omega
  | .app f a, n, h => by
      obtain ⟨hf, hn₁⟩ := Term.fill_spec f h
      obtain ⟨ha, hn₂⟩ := Term.fill_spec a (Nat.lt_of_lt_of_le h hn₁)
      simp only [Term.fill, Term.hasHole, hf, ha, Bool.or_false, true_and]
      omega

theorem Term.hasHole_of_annotsGround : ∀ {t : Term N}, t.AnnotsGround → t.hasHole = false
  | .var _, _ => rfl
  | .lam _ τ b, ⟨hτ, hb⟩ => by
      simp [Term.hasHole, Ty.hasHole_of_isGround hτ, Term.hasHole_of_annotsGround hb]
  | .app f a, ⟨hf, ha⟩ => by
      simp [Term.hasHole, Term.hasHole_of_annotsGround hf, Term.hasHole_of_annotsGround ha]

/-! ## Declarations and programs -/

/-- Does `_` occur in a declaration's type or body? -/
def cmdHasHole : Command N (Term N) Ty → Bool
  | .decl _ τ t => τ.hasHole || t.hasHole

def cmdMaxMvar : Command N (Term N) Ty → Nat
  | .decl _ τ t => max τ.maxMvar t.maxMvar

/-- Number a declaration's `_`s from `n` on: its type's, then its body's. -/
def cmdFill : Command N (Term N) Ty → Nat → Command N (Term N) Ty × Nat
  | .decl x τ t, n => (.decl x (τ.fill n).1 (t.fill (τ.fill n).2).1, (t.fill (τ.fill n).2).2)

theorem cmdFill_of_noHole {c : Command N (Term N) Ty} (h : cmdHasHole c = false) (n : Nat) :
    cmdFill c n = (c, n) := by
  obtain ⟨x, τ, t⟩ := c
  simp only [cmdHasHole, Bool.or_eq_false_iff] at h
  simp only [cmdFill, Ty.fill_of_noHole h.1, Term.fill_of_noHole h.2]

theorem cmdFill_spec (c : Command N (Term N) Ty) {n : Nat} (h : 0 < n) :
    cmdHasHole (cmdFill c n).1 = false ∧ n ≤ (cmdFill c n).2 := by
  obtain ⟨x, τ, t⟩ := c
  obtain ⟨hτ, hn₁⟩ := Ty.fill_spec τ h
  obtain ⟨ht, hn₂⟩ := Term.fill_spec t (Nat.lt_of_lt_of_le h hn₁)
  simp only [cmdFill, cmdHasHole, hτ, ht, Bool.or_false, true_and]
  omega

/-- Number the `_`s of a run of declarations from `n` on. -/
def fillList : List (Command N (Term N) Ty) → Nat → List (Command N (Term N) Ty)
  | [], _ => []
  | c :: cs, n => (cmdFill c n).1 :: fillList cs (cmdFill c n).2

theorem fillList_of_noHole : ∀ {cs : List (Command N (Term N) Ty)},
    (∀ c ∈ cs, cmdHasHole c = false) → ∀ n, fillList cs n = cs
  | [], _, _ => rfl
  | c :: cs, h, n => by
      simp only [fillList, cmdFill_of_noHole (h c List.mem_cons_self),
        fillList_of_noHole (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]

theorem fillList_noHole : ∀ (cs : List (Command N (Term N) Ty)) {n : Nat}, 0 < n →
    ∀ c ∈ fillList cs n, cmdHasHole c = false
  | [], _, _, _, hc => by simp [fillList] at hc
  | c :: cs, n, h, c', hc' => by
      obtain ⟨hc, hn⟩ := cmdFill_spec c h
      simp only [fillList, List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact hc
      · exact fillList_noHole cs (Nat.lt_of_lt_of_le h hn) c' hc'

/-- **Number every `_` of a program**, left to right, above every metavariable it mentions. -/
def fillHoles (p : Program N (Term N) Ty) : Program N (Term N) Ty :=
  let start := (p.toList.map cmdMaxMvar).foldl max 0 + 1
  ((cmdFill p.1 start).1, fillList p.2 (cmdFill p.1 start).2)

theorem fillHoles_of_noHole {p : Program N (Term N) Ty}
    (h : ∀ c ∈ p.toList, cmdHasHole c = false) : fillHoles p = p := by
  obtain ⟨c, cs⟩ := p
  simp only [NEList.toList, List.mem_cons] at h
  simp only [fillHoles, cmdFill_of_noHole (h c (.inl rfl)),
    fillList_of_noHole (fun c' hc' => h c' (.inr hc'))]

theorem fillHoles_noHole (p : Program N (Term N) Ty) : ∀ c ∈ (fillHoles p).toList,
    cmdHasHole c = false := by
  obtain ⟨c, cs⟩ := p
  intro c' hc'
  simp only [fillHoles, NEList.toList, List.mem_cons] at hc'
  have hpos : 0 < ((NEList.toList (c, cs)).map cmdMaxMvar).foldl max 0 + 1 := by omega
  obtain ⟨hc, hn⟩ := cmdFill_spec c hpos
  rcases hc' with rfl | hc'
  · exact hc
  · exact fillList_noHole cs (Nat.lt_of_lt_of_le hpos hn) c' hc'

/-- **Filling is idempotent**: a filled program has no `_` left to fill. -/
theorem fillHoles_idem (p : Program N (Term N) Ty) : fillHoles (fillHoles p) = fillHoles p :=
  fillHoles_of_noHole (fillHoles_noHole p)

theorem HasTypeGround.noHole [Atom N] : ∀ {Γ : Ctx N} {cs : List (Command N (Term N) Ty)},
    HasTypeGround Γ cs → ∀ c ∈ cs, cmdHasHole c = false
  | _, [], _, _, hc => by simp at hc
  | _, _ :: _, .decl _ hτ ht hrest, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [cmdHasHole, Ty.hasHole_of_isGround (Ty.ground_iff.mpr hτ),
          Term.hasHole_of_annotsGround (Term.annotsGround_iff_ground.mpr ht)]
      · exact HasTypeGround.noHole hrest c hc

/-- **Filling leaves a well-typed program alone**: it is ground, so it has no `_`. -/
theorem fillHoles_of_hasType [Atom N] {q : Program N (Term N) Ty}
    (h : TypeSystem.Named.Vernacular.HasType q) : fillHoles q = q :=
  fillHoles_of_noHole (HasTypeGround.noHole h)

end LambdaLab.Languages.Stlc.Named
