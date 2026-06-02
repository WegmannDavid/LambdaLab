import LambdaLab.Parser.Playground.Completeness

/-!
# Uniqueness: a syntactic criterion forcing `flatten` to be injective

`flatten` maps a parse tree to its token stream. A grammar is *unambiguous* when
`flatten` is injective on top-level `Expr`s. This file proves a checkable
syntactic criterion `Unambiguous G` (distinct name tokens + forest-shaped
precedence) implies `FlattenInjective G`.

The proof is a mutual prefix-form unique-decomposition over the whole tree
family. It works because `Tree.lean` keeps **every operand strictly tighter**
than its operator: an operator's separator token lives at the operator's own
(looser) level, so by acyclicity it can never sit at a top-level operand
boundary of any operand. The `Stops` predicate captures exactly this — "the
leftover after a tree does not begin with a token that could continue it" — and
is what makes the prefix-form generalization *true* (it is false without it:
`x` is a prefix of `x + y`).
-/

set_option maxHeartbeats 1000000

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-- A grammar is **unambiguous** when `flatten` is injective on top-level
expressions: no two distinct trees flatten to the same token string. -/
def FlattenInjective (G : Grammar) : Prop :=
  ∀ e₁ e₂ : Expr G, e₁.flatten = e₂.flatten → e₁ = e₂

/-- A checkable sufficient criterion: distinct name tokens + forest-shaped
precedence. -/
structure Unambiguous (G : Grammar) : Prop where
  nameParts_nodup : ∀ a : G.Op, (G.operator a).nameParts.Nodup
  nameParts_disjoint : ∀ a b : G.Op, a ≠ b →
    ∀ tk ∈ (G.operator a).nameParts, tk ∉ (G.operator b).nameParts
  tighter_disjoint : ∀ (a b₁ b₂ : G.Op), b₁ ∈ G.tighter a → b₂ ∈ G.tighter a → b₁ ≠ b₂ →
    ∀ c, TighterEq G.tighter b₁ c → TighterEq G.tighter b₂ c → False
  loosest_disjoint : ∀ (r₁ r₂ : G.Op), r₁ ∈ G.loosest → r₂ ∈ G.loosest → r₁ ≠ r₂ →
    ∀ c, TighterEq G.tighter r₁ c → TighterEq G.tighter r₂ c → False

/-! ## Reachability lemmas -/

theorem TighterEq.eq_of_sink {t : G.Op → List G.Op} {a c : G.Op}
    (hsink : t a = []) (h : TighterEq t a c) : c = a := by
  cases h with
  | refl => rfl
  | step hmem _ => rw [hsink] at hmem; exact absurd hmem List.not_mem_nil

theorem TighterEq.trans {t : G.Op → List G.Op} {a b c : G.Op}
    (h₁ : TighterEq t a b) (h₂ : TighterEq t b c) : TighterEq t a c := by
  induction h₁ with
  | refl => exact h₂
  | step hmem _ ih => exact TighterEq.step hmem (ih h₂)

/-- No cycle: if `b` is immediately tighter than `a`, then `a` is not reachable
from `b`. -/
theorem no_cycle {a b : G.Op} (h : b ∈ G.tighter a) :
    ¬ TighterEq G.tighter b a := by
  suffices H : ∀ a, ∀ b, b ∈ G.tighter a → TighterEq G.tighter b a → False from H a b h
  intro a
  induction a using G.tighter_wf.induction with
  | _ a ih =>
    intro b hRba hreach
    cases hreach with
    | refl => exact ih a hRba a hRba TighterEq.refl
    | step hRcb hca =>
        rename_i c
        have hcb : TighterEq G.tighter c b :=
          hca.trans (TighterEq.step hRba TighterEq.refl)
        exact ih b hRba c hRcb hcb

/-! ## Name-part lemmas -/

theorem Operator.head_mem (o : Operator) : o.head ∈ o.nameParts :=
  List.head_mem o.nameParts_ne

theorem Unambiguous.heads_distinct (hG : Unambiguous G) {o o' : G.Op} (h : o ≠ o') :
    (G.operator o).head ≠ (G.operator o').head := by
  intro he
  have h1 : (G.operator o).head ∈ (G.operator o).nameParts := Operator.head_mem _
  have h2 : (G.operator o').head ∈ (G.operator o').nameParts := Operator.head_mem _
  rw [← he] at h2
  exact hG.nameParts_disjoint o o' h _ h1 h2

/-- A non-leading name-part of `a` is the head of *no* operator. -/
theorem nameParts_notHead (hG : Unambiguous G) {a tk} (hmem : tk ∈ (G.operator a).nameParts)
    (hne : tk ≠ (G.operator a).head) : ∀ o : G.Op, (G.operator o).head ≠ tk := by
  intro o he
  have hmo : tk ∈ (G.operator o).nameParts := he ▸ Operator.head_mem (G.operator o)
  by_cases hoa : o = a
  · subst hoa; exact hne he.symm
  · exact hG.nameParts_disjoint a o (fun h => hoa h.symm) tk hmem hmo

/-- Every name-part *after the head* is the head of no operator. -/
theorem nameParts_tail_notHead (hG : Unambiguous G) (a : G.Op) :
    ∀ tk ∈ (G.operator a).nameParts.tail, ∀ o : G.Op, (G.operator o).head ≠ tk := by
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (G.operator a).nameParts_ne
  have hnod : (x :: xs).Nodup := hx ▸ hG.nameParts_nodup a
  have hxnotin : x ∉ xs := (List.nodup_cons.mp hnod).1
  have hhd : (G.operator a).head = x := by
    unfold Operator.head; simp [hx]
  intro tk htk
  rw [hx, List.tail_cons] at htk
  refine nameParts_notHead hG (by rw [hx]; exact List.mem_cons_of_mem x htk) ?_
  rw [hhd]; intro he; subst he; exact hxnotin htk

/-! ## head? helpers -/

theorem head?_append_left {l s : List Token} (h : l ≠ []) :
    (l ++ s).head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem head?_eq_of_prefix {l₁ l₂ s₁ s₂ : List Token}
    (h : l₁ ++ s₁ = l₂ ++ s₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    l₁.head? = l₂.head? := by
  have : (l₁ ++ s₁).head? = (l₂ ++ s₂).head? := by rw [h]
  rwa [head?_append_left h₁, head?_append_left h₂] at this

/-! ## flatten is never empty -/

mutual
  theorem Tree.flatten_ne {b : G.Op} (t : Tree G b) : t.flatten ≠ [] := by
    match t with
    | .op _ ch => simpa only [Tree.flatten] using ch.flatten_ne
    | .next tb => simpa only [Tree.flatten] using tb.flatten_ne

  theorem TreeBelow.flatten_ne {b : G.Op} (t : TreeBelow G b) : t.flatten ≠ [] := by
    match t with
    | .mk _ _ tc => simpa only [TreeBelow.flatten] using tc.flatten_ne

  theorem Children.flatten_ne {b : G.Op} {f : Fixity} (ch : Children G b f) :
      ch.flatten ≠ [] := by
    match ch with
    | .closed w => simpa only [Children.flatten] using w.flatten_ne
    | .«prefix» ps => simpa only [Children.flatten] using ps.flatten_ne
    | .«postfix» tb pt =>
        simp only [Children.flatten]; intro h
        exact tb.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .infixL hd tl =>
        simp only [Children.flatten]; intro h
        exact hd.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .infixR hd tl =>
        simp only [Children.flatten]; intro h
        exact hd.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .infixN l w r =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1

  theorem PrefixStack.flatten_ne {b : G.Op} (ps : PrefixStack G b) : ps.flatten ≠ [] := by
    match ps with
    | .last w tb =>
        simp only [PrefixStack.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .more w ps =>
        simp only [PrefixStack.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1

  theorem PostfixTail.flatten_ne {b : G.Op} (pt : PostfixTail G b) : pt.flatten ≠ [] := by
    match pt with
    | .last w => simpa only [PostfixTail.flatten] using w.flatten_ne
    | .cons w t =>
        simp only [PostfixTail.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1

  theorem InfixTail.flatten_ne {b : G.Op} (tl : InfixTail G b) : tl.flatten ≠ [] := by
    match tl with
    | .last w tb =>
        simp only [InfixTail.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .cons w tb t =>
        simp only [InfixTail.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1

  theorem Woven.flatten_ne {parts : List Token} (w : Woven G parts) : w.flatten ≠ [] := by
    match w with
    | .last _ => simp [Woven.flatten]
    | .cons _ _ _ => simp [Woven.flatten]
end

/-! ## Leading-token facts -/

theorem Woven.flatten_head {parts : List Token} (w : Woven G parts) :
    w.flatten.head? = parts.head? := by
  match w with
  | .last tk => rfl
  | .cons tk e w => rfl

theorem Woven.flatten_head_op {a : G.Op} (w : Woven G (G.operator a).nameParts) :
    w.flatten.head? = some (G.operator a).head := by
  rw [Woven.flatten_head, List.head?_eq_some_head (G.operator a).nameParts_ne]; rfl

theorem Woven.flatten_head_mem {parts : List Token} (w : Woven G parts) {t : Token}
    (ht : w.flatten.head? = some t) : t ∈ parts := by
  rw [Woven.flatten_head] at ht
  cases parts with
  | nil => simp at ht
  | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at ht
      subst ht; simp

theorem PrefixStack.flatten_head_op {a : G.Op} (p : PrefixStack G a) :
    p.flatten.head? = some (G.operator a).head := by
  cases p with
  | last w tb =>
      simp only [PrefixStack.flatten]; rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
  | more w ps =>
      simp only [PrefixStack.flatten]; rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op

theorem PostfixTail.flatten_head_op {a : G.Op} (p : PostfixTail G a) :
    p.flatten.head? = some (G.operator a).head := by
  cases p with
  | last w => simpa only [PostfixTail.flatten] using w.flatten_head_op
  | cons w t =>
      simp only [PostfixTail.flatten]; rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op

theorem InfixTail.flatten_head_op {a : G.Op} (p : InfixTail G a) :
    p.flatten.head? = some (G.operator a).head := by
  cases p with
  | last w tb =>
      simp only [InfixTail.flatten]; rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
  | cons w tb t =>
      simp only [InfixTail.flatten, List.append_assoc]
      rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op

mutual
  theorem Tree.headTok_reach {b : G.Op} (t : Tree G b) :
      ∃ o, TighterEq G.tighter b o ∧ t.flatten.head? = some (G.operator o).head := by
    match t with
    | .op a ch =>
        obtain ⟨o, hr, hh⟩ := ch.headTok_reach
        exact ⟨o, hr, by simpa only [Tree.flatten] using hh⟩
    | .next tb =>
        obtain ⟨o, hr, hh⟩ := tb.headTok_reach
        exact ⟨o, hr, by simpa only [Tree.flatten] using hh⟩

  theorem TreeBelow.headTok_reach {a : G.Op} (tb : TreeBelow G a) :
      ∃ o, TighterEq G.tighter a o ∧ tb.flatten.head? = some (G.operator o).head := by
    match tb with
    | .mk b hmem t =>
        obtain ⟨o, hr, hh⟩ := t.headTok_reach
        exact ⟨o, TighterEq.step hmem hr, by simpa only [TreeBelow.flatten] using hh⟩

  theorem Children.headTok_reach {a : G.Op} {f : Fixity} (ch : Children G a f) :
      ∃ o, TighterEq G.tighter a o ∧ ch.flatten.head? = some (G.operator o).head := by
    match ch with
    | .closed w =>
        exact ⟨a, TighterEq.refl, by simpa only [Children.flatten] using w.flatten_head_op⟩
    | .«prefix» ps =>
        exact ⟨a, TighterEq.refl, by simpa only [Children.flatten] using ps.flatten_head_op⟩
    | .«postfix» tb pt =>
        obtain ⟨o, hr, hh⟩ := tb.headTok_reach
        refine ⟨o, hr, ?_⟩
        simp only [Children.flatten]; rw [head?_append_left tb.flatten_ne]; exact hh
    | .infixL hd tl =>
        obtain ⟨o, hr, hh⟩ := hd.headTok_reach
        refine ⟨o, hr, ?_⟩
        simp only [Children.flatten]; rw [head?_append_left hd.flatten_ne]; exact hh
    | .infixR hd tl =>
        obtain ⟨o, hr, hh⟩ := hd.headTok_reach
        refine ⟨o, hr, ?_⟩
        simp only [Children.flatten]; rw [head?_append_left hd.flatten_ne]; exact hh
    | .infixN l w r =>
        obtain ⟨o, hr, hh⟩ := l.headTok_reach
        refine ⟨o, hr, ?_⟩
        simp only [Children.flatten, List.append_assoc]
        rw [head?_append_left l.flatten_ne]; exact hh
end

/-! ## The `Stops` predicate -/

/-- The leftover `s` does not begin with a token that could continue a tree at
level `a`: no operator reachable from `a` has its head there. (Vacuous when
`s = []`.) This is exactly what makes prefix-form unique decomposition true. -/
def Stops (a : G.Op) (s : List Token) : Prop :=
  ∀ o, TighterEq G.tighter a o → s.head? ≠ some (G.operator o).head

/-- `s` begins with no operator's head at all (stops every level). -/
def StopsAll (s : List Token) : Prop :=
  ∀ o : G.Op, s.head? ≠ some (G.operator o).head

/-- `s` stops every operator strictly tighter than `a` (what a `TreeBelow G a`
needs of its leftover). -/
def StopsBelow (a : G.Op) (s : List Token) : Prop :=
  ∀ b, b ∈ G.tighter a → Stops b s

theorem StopsAll.stops {s : List Token} (h : StopsAll (G := G) s) (a : G.Op) : Stops a s :=
  fun o _ => h o

theorem Stops.mono {a b : G.Op} {s : List Token} (hab : TighterEq G.tighter a b)
    (h : Stops a s) : Stops b s :=
  fun o hbo => h o (hab.trans hbo)

theorem Stops.below {a : G.Op} {s : List Token} (h : Stops a s) : StopsBelow a s :=
  fun _b hb => h.mono (TighterEq.step hb TighterEq.refl)

/-- A leftover beginning with `a`'s own head stops everything strictly tighter
than `a` (acyclicity: `a` is unreachable from anything tighter). -/
theorem StopsBelow_of_head (hG : Unambiguous G) {a : G.Op} {s : List Token}
    (h : s.head? = some (G.operator a).head) : StopsBelow a s := by
  intro b hb o hbo hcon
  rw [h] at hcon
  have heq : (G.operator a).head = (G.operator o).head := Option.some.inj hcon
  have hoa : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heq
  exact no_cycle hb (hoa ▸ hbo)

/-- `Woven G []` is uninhabited. -/
theorem Woven.not_nil (w : Woven G []) : False := by cases w

/-- Constructor equality for `TreeBelow.mk` across a level cast. -/
theorem TreeBelow.mk_cast_eq {a b₁ b₂ : G.Op} (hb : b₁ = b₂)
    {hb₁ : b₁ ∈ G.tighter a} {hb₂ : b₂ ∈ G.tighter a}
    {u₁ : Tree G b₁} {u₂ : Tree G b₂} (hu : hb ▸ u₁ = u₂) :
    (TreeBelow.mk b₁ hb₁ u₁ : TreeBelow G a) = TreeBelow.mk b₂ hb₂ u₂ := by
  subst hb; subst hu; rfl

/-- Constructor equality for `Expr.mk` across a root cast. -/
theorem Expr.mk_cast_eq {r₁ r₂ : G.Op} (hr : r₁ = r₂)
    {hr₁ : r₁ ∈ G.loosest} {hr₂ : r₂ ∈ G.loosest}
    {t₁ : Tree G r₁} {t₂ : Tree G r₂} (hu : hr ▸ t₁ = t₂) :
    (Expr.mk r₁ hr₁ t₁ : Expr G) = Expr.mk r₂ hr₂ t₂ := by
  subst hr; subst hu; rfl

theorem mem_of_mem_tail {α} {l : List α} {t : α} (h : t ∈ l.tail) : t ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp only [List.tail_cons] at h; exact List.mem_cons_of_mem x h

/-! ## Mutual unique decomposition (prefix form, with `Stops`) -/

mutual
  theorem udTree (hG : Unambiguous G) {a : G.Op} (t₁ t₂ : Tree G a) (s₁ s₂ : List Token)
      (h : t₁.flatten ++ s₁ = t₂.flatten ++ s₂) (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) :
      t₁ = t₂ ∧ s₁ = s₂ := by
    match t₁, t₂ with
    | .op _ c₁, .op _ c₂ =>
        have heqc : c₁.flatten ++ s₁ = c₂.flatten ++ s₂ := by simpa only [Tree.flatten] using h
        have hc := udChildren hG c₁ c₂ s₁ s₂ heqc hs₁ hs₂
        exact ⟨by rw [hc.1], hc.2⟩
    | .op _ c, .next tb =>
        obtain ⟨b, hb, u⟩ := tb
        refine (udOpNext hG c b hb u s₁ s₂ ?_ hs₁ hs₂).elim
        simpa only [Tree.flatten, TreeBelow.flatten] using h
    | .next tb, .op _ c =>
        obtain ⟨b, hb, u⟩ := tb
        refine (udOpNext hG c b hb u s₂ s₁ ?_ hs₂ hs₁).elim
        simpa only [Tree.flatten, TreeBelow.flatten] using h.symm
    | .next tb₁, .next tb₂ =>
        have heq : tb₁.flatten ++ s₁ = tb₂.flatten ++ s₂ := by simpa only [Tree.flatten] using h
        have ht := udTreeBelow hG tb₁ tb₂ s₁ s₂ heq hs₁.below hs₂.below
        exact ⟨by rw [ht.1], ht.2⟩
  termination_by sizeOf t₁ + sizeOf t₂

  theorem udTreeBelow (hG : Unambiguous G) {a : G.Op} (tb₁ tb₂ : TreeBelow G a)
      (s₁ s₂ : List Token) (h : tb₁.flatten ++ s₁ = tb₂.flatten ++ s₂)
      (hs₁ : StopsBelow a s₁) (hs₂ : StopsBelow a s₂) : tb₁ = tb₂ ∧ s₁ = s₂ := by
    match tb₁, tb₂ with
    | .mk b₁ hb₁ u₁, .mk b₂ hb₂ u₂ =>
      have heq : u₁.flatten ++ s₁ = u₂.flatten ++ s₂ := by simpa only [TreeBelow.flatten] using h
      have hhd : u₁.flatten.head? = u₂.flatten.head? :=
        head?_eq_of_prefix heq u₁.flatten_ne u₂.flatten_ne
      obtain ⟨o₁, hr₁, hh₁⟩ := u₁.headTok_reach
      obtain ⟨o₂, hr₂, hh₂⟩ := u₂.headTok_reach
      have hheads : (G.operator o₁).head = (G.operator o₂).head := by
        rw [hh₁, hh₂] at hhd; exact Option.some.inj hhd
      have ho : o₁ = o₂ := Classical.byContradiction fun hne => hG.heads_distinct hne hheads
      subst ho
      by_cases hb : b₁ = b₂
      · have heq' : (hb ▸ u₁).flatten ++ s₁ = u₂.flatten ++ s₂ := by cases hb; exact heq
        have hrec := udTree hG (hb ▸ u₁) u₂ s₁ s₂ heq' (hs₁ b₂ (hb ▸ hb₁)) (hs₂ b₂ hb₂)
        exact ⟨TreeBelow.mk_cast_eq hb hrec.1, hrec.2⟩
      · exact (hG.tighter_disjoint a b₁ b₂ hb₁ hb₂ hb o₁ hr₁ hr₂).elim
  termination_by sizeOf tb₁ + sizeOf tb₂
  decreasing_by subst_vars; simp_wf <;> omega

  theorem udChildren (hG : Unambiguous G) {a : G.Op} {f : Fixity}
      (c₁ c₂ : Children G a f) (s₁ s₂ : List Token)
      (h : c₁.flatten ++ s₁ = c₂.flatten ++ s₂) (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) :
      c₁ = c₂ ∧ s₁ = s₂ := by
    match c₁, c₂ with
    | .closed w₁, .closed w₂ =>
        have heq : w₁.flatten ++ s₁ = w₂.flatten ++ s₂ := by simpa only [Children.flatten] using h
        have hrec := udWoven hG w₁ w₂ s₁ s₂ heq (nameParts_tail_notHead hG a)
        exact ⟨by rw [hrec.1], hrec.2⟩
    | .«prefix» p₁, .«prefix» p₂ =>
        have heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂ := by simpa only [Children.flatten] using h
        have hrec := udPrefixStack hG p₁ p₂ s₁ s₂ heq hs₁ hs₂
        exact ⟨by rw [hrec.1], hrec.2⟩
    | .«postfix» tb₁ pt₁, .«postfix» tb₂ pt₂ =>
        have heq : tb₁.flatten ++ (pt₁.flatten ++ s₁) = tb₂.flatten ++ (pt₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have htb := udTreeBelow hG tb₁ tb₂ (pt₁.flatten ++ s₁) (pt₂.flatten ++ s₂) heq
          (StopsBelow_of_head hG (by rw [head?_append_left pt₁.flatten_ne]; exact pt₁.flatten_head_op))
          (StopsBelow_of_head hG (by rw [head?_append_left pt₂.flatten_ne]; exact pt₂.flatten_head_op))
        have hpt := udPostfixTail hG pt₁ pt₂ s₁ s₂ htb.2 hs₁ hs₂
        exact ⟨by rw [htb.1, hpt.1], hpt.2⟩
    | .infixL hd₁ tl₁, .infixL hd₂ tl₂ =>
        have heq : hd₁.flatten ++ (tl₁.flatten ++ s₁) = hd₂.flatten ++ (tl₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hhd := udTreeBelow hG hd₁ hd₂ (tl₁.flatten ++ s₁) (tl₂.flatten ++ s₂) heq
          (StopsBelow_of_head hG (by rw [head?_append_left tl₁.flatten_ne]; exact tl₁.flatten_head_op))
          (StopsBelow_of_head hG (by rw [head?_append_left tl₂.flatten_ne]; exact tl₂.flatten_head_op))
        have htl := udInfixTail hG tl₁ tl₂ s₁ s₂ hhd.2 hs₁ hs₂
        exact ⟨by rw [hhd.1, htl.1], htl.2⟩
    | .infixR hd₁ tl₁, .infixR hd₂ tl₂ =>
        have heq : hd₁.flatten ++ (tl₁.flatten ++ s₁) = hd₂.flatten ++ (tl₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hhd := udTreeBelow hG hd₁ hd₂ (tl₁.flatten ++ s₁) (tl₂.flatten ++ s₂) heq
          (StopsBelow_of_head hG (by rw [head?_append_left tl₁.flatten_ne]; exact tl₁.flatten_head_op))
          (StopsBelow_of_head hG (by rw [head?_append_left tl₂.flatten_ne]; exact tl₂.flatten_head_op))
        have htl := udInfixTail hG tl₁ tl₂ s₁ s₂ hhd.2 hs₁ hs₂
        exact ⟨by rw [hhd.1, htl.1], htl.2⟩
    | .infixN l₁ w₁ r₁, .infixN l₂ w₂ r₂ =>
        have heq : l₁.flatten ++ (w₁.flatten ++ (r₁.flatten ++ s₁))
                 = l₂.flatten ++ (w₂.flatten ++ (r₂.flatten ++ s₂)) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hl := udTreeBelow hG l₁ l₂ (w₁.flatten ++ (r₁.flatten ++ s₁))
          (w₂.flatten ++ (r₂.flatten ++ s₂)) heq
          (StopsBelow_of_head hG (by rw [head?_append_left w₁.flatten_ne]; exact w₁.flatten_head_op))
          (StopsBelow_of_head hG (by rw [head?_append_left w₂.flatten_ne]; exact w₂.flatten_head_op))
        have hw := udWoven hG w₁ w₂ (r₁.flatten ++ s₁) (r₂.flatten ++ s₂) hl.2
          (nameParts_tail_notHead hG a)
        have hr := udTreeBelow hG r₁ r₂ s₁ s₂ hw.2 hs₁.below hs₂.below
        exact ⟨by rw [hl.1, hw.1, hr.1], hr.2⟩
  termination_by sizeOf c₁ + sizeOf c₂

  theorem udPrefixStack (hG : Unambiguous G) {a : G.Op} (p₁ p₂ : PrefixStack G a)
      (s₁ s₂ : List Token) (h : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    match p₁, p₂ with
    | .last w₁ tb₁, .last w₂ tb₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁) = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [PrefixStack.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have htb := udTreeBelow hG tb₁ tb₂ s₁ s₂ hw.2 hs₁.below hs₂.below
        exact ⟨by rw [hw.1, htb.1], htb.2⟩
    | .last w₁ tb₁, .more w₂ p₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁) = w₂.flatten ++ (p₂.flatten ++ s₂) := by
          simpa only [PrefixStack.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (p₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        -- tb₁ leads with a tighter operator's head; p₂ leads with a.head — contradiction.
        obtain ⟨b, hb, lt⟩ := tb₁
        obtain ⟨o, hr, hh⟩ := lt.headTok_reach
        have hhd : (TreeBelow.mk b hb lt).flatten.head? = p₂.flatten.head? :=
          head?_eq_of_prefix hw.2 (TreeBelow.mk b hb lt).flatten_ne p₂.flatten_ne
        rw [p₂.flatten_head_op] at hhd
        simp only [TreeBelow.flatten] at hhd
        rw [hh] at hhd
        have heq2 : (G.operator o).head = (G.operator a).head := Option.some.inj hhd
        have hoa : o = a := Classical.byContradiction fun hne => hG.heads_distinct hne heq2
        exact (no_cycle hb (hoa ▸ hr)).elim
    | .more w₁ p₁, .last w₂ tb₂ =>
        have heq : w₁.flatten ++ (p₁.flatten ++ s₁) = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [PrefixStack.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (p₁.flatten ++ s₁) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        obtain ⟨b, hb, lt⟩ := tb₂
        obtain ⟨o, hr, hh⟩ := lt.headTok_reach
        have hhd : p₁.flatten.head? = (TreeBelow.mk b hb lt).flatten.head? :=
          head?_eq_of_prefix hw.2 p₁.flatten_ne (TreeBelow.mk b hb lt).flatten_ne
        rw [p₁.flatten_head_op] at hhd
        simp only [TreeBelow.flatten] at hhd
        rw [hh] at hhd
        have heq2 : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
        have hoa : o = a := Classical.byContradiction fun hne => hG.heads_distinct hne heq2.symm
        exact (no_cycle hb (hoa ▸ hr)).elim
    | .more w₁ p₁, .more w₂ p₂ =>
        have heq : w₁.flatten ++ (p₁.flatten ++ s₁) = w₂.flatten ++ (p₂.flatten ++ s₂) := by
          simpa only [PrefixStack.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (p₁.flatten ++ s₁) (p₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have hp := udPrefixStack hG p₁ p₂ s₁ s₂ hw.2 hs₁ hs₂
        exact ⟨by rw [hw.1, hp.1], hp.2⟩
  termination_by sizeOf p₁ + sizeOf p₂

  theorem udPostfixTail (hG : Unambiguous G) {a : G.Op} (p₁ p₂ : PostfixTail G a)
      (s₁ s₂ : List Token) (h : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    match p₁, p₂ with
    | .last w₁, .last w₂ =>
        have heq : w₁.flatten ++ s₁ = w₂.flatten ++ s₂ := by
          simpa only [PostfixTail.flatten] using h
        have hw := udWoven hG w₁ w₂ s₁ s₂ heq (nameParts_tail_notHead hG a)
        exact ⟨by rw [hw.1], hw.2⟩
    | .last w₁, .cons w₂ t₂ =>
        have heq : w₁.flatten ++ s₁ = w₂.flatten ++ (t₂.flatten ++ s₂) := by
          simpa only [PostfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ s₁ (t₂.flatten ++ s₂) heq (nameParts_tail_notHead hG a)
        exact absurd (by rw [hw.2, head?_append_left t₂.flatten_ne]; exact t₂.flatten_head_op)
          (hs₁ a TighterEq.refl)
    | .cons w₁ t₁, .last w₂ =>
        have heq : w₁.flatten ++ (t₁.flatten ++ s₁) = w₂.flatten ++ s₂ := by
          simpa only [PostfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (t₁.flatten ++ s₁) s₂ heq (nameParts_tail_notHead hG a)
        exact absurd (by rw [← hw.2, head?_append_left t₁.flatten_ne]; exact t₁.flatten_head_op)
          (hs₂ a TighterEq.refl)
    | .cons w₁ t₁, .cons w₂ t₂ =>
        have heq : w₁.flatten ++ (t₁.flatten ++ s₁) = w₂.flatten ++ (t₂.flatten ++ s₂) := by
          simpa only [PostfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (t₁.flatten ++ s₁) (t₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have ht := udPostfixTail hG t₁ t₂ s₁ s₂ hw.2 hs₁ hs₂
        exact ⟨by rw [hw.1, ht.1], ht.2⟩
  termination_by sizeOf p₁ + sizeOf p₂

  theorem udInfixTail (hG : Unambiguous G) {a : G.Op} (p₁ p₂ : InfixTail G a)
      (s₁ s₂ : List Token) (h : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    match p₁, p₂ with
    | .last w₁ tb₁, .last w₂ tb₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁) = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [InfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have htb := udTreeBelow hG tb₁ tb₂ s₁ s₂ hw.2 hs₁.below hs₂.below
        exact ⟨by rw [hw.1, htb.1], htb.2⟩
    | .last w₁ tb₁, .cons w₂ tb₂ t₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁)
                 = w₂.flatten ++ (tb₂.flatten ++ (t₂.flatten ++ s₂)) := by
          simpa only [InfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (tb₂.flatten ++ (t₂.flatten ++ s₂)) heq
          (nameParts_tail_notHead hG a)
        have htb := udTreeBelow hG tb₁ tb₂ s₁ (t₂.flatten ++ s₂) hw.2 hs₁.below
          (StopsBelow_of_head hG (by rw [head?_append_left t₂.flatten_ne]; exact t₂.flatten_head_op))
        exact absurd (by rw [htb.2, head?_append_left t₂.flatten_ne]; exact t₂.flatten_head_op)
          (hs₁ a TighterEq.refl)
    | .cons w₁ tb₁ t₁, .last w₂ tb₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ (t₁.flatten ++ s₁))
                 = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [InfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ (t₁.flatten ++ s₁)) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have htb := udTreeBelow hG tb₁ tb₂ (t₁.flatten ++ s₁) s₂ hw.2
          (StopsBelow_of_head hG (by rw [head?_append_left t₁.flatten_ne]; exact t₁.flatten_head_op))
          hs₂.below
        exact absurd (by rw [← htb.2, head?_append_left t₁.flatten_ne]; exact t₁.flatten_head_op)
          (hs₂ a TighterEq.refl)
    | .cons w₁ tb₁ t₁, .cons w₂ tb₂ t₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ (t₁.flatten ++ s₁))
                 = w₂.flatten ++ (tb₂.flatten ++ (t₂.flatten ++ s₂)) := by
          simpa only [InfixTail.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ (t₁.flatten ++ s₁))
          (tb₂.flatten ++ (t₂.flatten ++ s₂)) heq (nameParts_tail_notHead hG a)
        have htb := udTreeBelow hG tb₁ tb₂ (t₁.flatten ++ s₁) (t₂.flatten ++ s₂) hw.2
          (StopsBelow_of_head hG (by rw [head?_append_left t₁.flatten_ne]; exact t₁.flatten_head_op))
          (StopsBelow_of_head hG (by rw [head?_append_left t₂.flatten_ne]; exact t₂.flatten_head_op))
        have ht := udInfixTail hG t₁ t₂ s₁ s₂ htb.2 hs₁ hs₂
        exact ⟨by rw [hw.1, htb.1, ht.1], ht.2⟩
  termination_by sizeOf p₁ + sizeOf p₂

  theorem udWoven (hG : Unambiguous G) {parts : List Token}
      (w₁ w₂ : Woven G parts) (s₁ s₂ : List Token)
      (h : w₁.flatten ++ s₁ = w₂.flatten ++ s₂)
      (hpr : ∀ tk ∈ parts.tail, ∀ o : G.Op, (G.operator o).head ≠ tk) :
      w₁ = w₂ ∧ s₁ = s₂ := by
    match w₁, w₂ with
    | .last tk, w₂ =>
        cases w₂ with
        | last tk' =>
            refine ⟨rfl, ?_⟩
            simpa only [Woven.flatten, List.cons_append, List.nil_append,
              List.cons.injEq, true_and] using h
        | cons tk' e w => exact (w.not_nil).elim
    | .cons tk e₁ w₁', w₂ =>
        cases w₂ with
        | last tk' => exact (w₁'.not_nil).elim
        | cons _ e₂ w₂' =>
        have heq : e₁.flatten ++ (w₁'.flatten ++ s₁) = e₂.flatten ++ (w₂'.flatten ++ s₂) := by
          have h' : [tk] ++ (e₁.flatten ++ (w₁'.flatten ++ s₁))
                  = [tk] ++ (e₂.flatten ++ (w₂'.flatten ++ s₂)) := by
            simpa only [Woven.flatten, List.append_assoc] using h
          exact List.append_cancel_left h'
        -- each interior hole is followed by the next name-part, which is nobody's head
        have hstop1 : StopsAll (G := G) (w₁'.flatten ++ s₁) := by
          intro o hcon
          rw [head?_append_left w₁'.flatten_ne] at hcon
          exact hpr _ (w₁'.flatten_head_mem hcon) o rfl
        have hstop2 : StopsAll (G := G) (w₂'.flatten ++ s₂) := by
          intro o hcon
          rw [head?_append_left w₂'.flatten_ne] at hcon
          exact hpr _ (w₂'.flatten_head_mem hcon) o rfl
        have hrec := udExpr hG e₁ e₂ (w₁'.flatten ++ s₁) (w₂'.flatten ++ s₂) heq hstop1 hstop2
        have hrec2 := udWoven hG w₁' w₂' s₁ s₂ hrec.2 (fun t ht => hpr t (mem_of_mem_tail ht))
        exact ⟨by rw [hrec.1, hrec2.1], hrec2.2⟩
  termination_by sizeOf w₁ + sizeOf w₂

  theorem udExpr (hG : Unambiguous G) (e₁ e₂ : Expr G) (s₁ s₂ : List Token)
      (h : e₁.flatten ++ s₁ = e₂.flatten ++ s₂) (hs₁ : StopsAll (G := G) s₁)
      (hs₂ : StopsAll (G := G) s₂) : e₁ = e₂ ∧ s₁ = s₂ := by
    match e₁, e₂ with
    | .mk r₁ hr₁ t₁, .mk r₂ hr₂ t₂ =>
      have heq : t₁.flatten ++ s₁ = t₂.flatten ++ s₂ := by simpa only [Expr.flatten] using h
      have hhd : t₁.flatten.head? = t₂.flatten.head? :=
        head?_eq_of_prefix heq t₁.flatten_ne t₂.flatten_ne
      obtain ⟨o₁, ho₁, hh₁⟩ := t₁.headTok_reach
      obtain ⟨o₂, ho₂, hh₂⟩ := t₂.headTok_reach
      have hheads : (G.operator o₁).head = (G.operator o₂).head := by
        rw [hh₁, hh₂] at hhd; exact Option.some.inj hhd
      have ho : o₁ = o₂ := Classical.byContradiction fun hne => hG.heads_distinct hne hheads
      subst ho
      by_cases hr : r₁ = r₂
      · have heq' : (hr ▸ t₁).flatten ++ s₁ = t₂.flatten ++ s₂ := by cases hr; exact heq
        have hrec := udTree hG (hr ▸ t₁) t₂ s₁ s₂ heq' (hs₁.stops r₂) (hs₂.stops r₂)
        exact ⟨Expr.mk_cast_eq hr hrec.1, hrec.2⟩
      · exact (hG.loosest_disjoint r₁ r₂ hr₁ hr₂ hr o₁ ho₁ ho₂).elim
  termination_by sizeOf e₁ + sizeOf e₂
  decreasing_by subst_vars; simp_wf <;> omega

  /-- The leading-operand argument for the infix/postfix `op`-vs-`next` cases.
  `tb` is the leading operand (strictly tighter than `a`); `mid` (the rest of the
  operator's flatten plus the outer leftover) begins with `a`'s separator head. -/
  theorem udLeadOp (hG : Unambiguous G) {a : G.Op} (tb : TreeBelow G a)
      (b : G.Op) (hb : b ∈ G.tighter a) (u : Tree G b) (mid s₂ : List Token)
      (hmid : mid.head? = some (G.operator a).head)
      (hlt : tb.flatten ++ mid = u.flatten ++ s₂) (hs₂ : Stops a s₂) : False := by
    match tb with
    | .mk b' hb' lt =>
      have hlt' : lt.flatten ++ mid = u.flatten ++ s₂ := by simpa only [TreeBelow.flatten] using hlt
      by_cases hbb : b' = b
      · have hsmid : Stops b' mid := by
          intro o ho hcon
          rw [hmid] at hcon
          have hh : (G.operator a).head = (G.operator o).head := Option.some.inj hcon
          have hae : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne hh
          exact (hae ▸ no_cycle hb') ho
        have heq' : (hbb ▸ lt).flatten ++ mid = u.flatten ++ s₂ := by cases hbb; exact hlt'
        have hrec := udTree hG (hbb ▸ lt) u mid s₂ heq' (hbb ▸ hsmid)
          (hs₂.mono (TighterEq.step hb TighterEq.refl))
        exact hs₂ a TighterEq.refl (by rw [← hrec.2]; exact hmid)
      · obtain ⟨o₁, hr₁, hh₁⟩ := lt.headTok_reach
        obtain ⟨o₂, hr₂, hh₂⟩ := u.headTok_reach
        have hhd : lt.flatten.head? = u.flatten.head? :=
          head?_eq_of_prefix hlt' lt.flatten_ne u.flatten_ne
        rw [hh₁, hh₂] at hhd
        have hoo : o₁ = o₂ := Classical.byContradiction fun hne => hG.heads_distinct hne (Option.some.inj hhd)
        subst hoo
        exact hG.tighter_disjoint a b' b hb' hb hbb o₁ hr₁ hr₂
  termination_by sizeOf tb + sizeOf u
  decreasing_by subst_vars; simp_wf <;> omega

  theorem udOpNext (hG : Unambiguous G) {a : G.Op} {f : Fixity}
      (c : Children G a f)
      (b : G.Op) (hb : b ∈ G.tighter a) (u : Tree G b) (s₁ s₂ : List Token)
      (heq : c.flatten ++ s₁ = u.flatten ++ s₂)
      (_hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : False := by
    match c, heq with
    | .closed w, heq =>
        obtain ⟨o, hr, hh⟩ := u.headTok_reach
        have hca : (Children.closed w).flatten.head? = some (G.operator a).head := by
          simpa only [Children.flatten] using w.flatten_head_op
        have hhd : (Children.closed w).flatten.head? = u.flatten.head? :=
          head?_eq_of_prefix heq (Children.closed w).flatten_ne u.flatten_ne
        rw [hca, hh] at hhd
        have heads : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
        have hoa : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heads
        exact no_cycle hb (hoa ▸ hr)
    | .«prefix» ps, heq =>
        obtain ⟨o, hr, hh⟩ := u.headTok_reach
        have hca : (Children.«prefix» ps).flatten.head? = some (G.operator a).head := by
          simpa only [Children.flatten] using ps.flatten_head_op
        have hhd : (Children.«prefix» ps).flatten.head? = u.flatten.head? :=
          head?_eq_of_prefix heq (Children.«prefix» ps).flatten_ne u.flatten_ne
        rw [hca, hh] at hhd
        have heads : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
        have hoa : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heads
        exact no_cycle hb (hoa ▸ hr)
    | .«postfix» tb pt, heq =>
        refine udLeadOp hG tb b hb u (pt.flatten ++ s₁) s₂ ?_ ?_ hs₂
        · rw [head?_append_left pt.flatten_ne]; exact pt.flatten_head_op
        · simpa only [Children.flatten, List.append_assoc] using heq
    | .infixL hd tl, heq =>
        refine udLeadOp hG hd b hb u (tl.flatten ++ s₁) s₂ ?_ ?_ hs₂
        · rw [head?_append_left tl.flatten_ne]; exact tl.flatten_head_op
        · simpa only [Children.flatten, List.append_assoc] using heq
    | .infixR hd tl, heq =>
        refine udLeadOp hG hd b hb u (tl.flatten ++ s₁) s₂ ?_ ?_ hs₂
        · rw [head?_append_left tl.flatten_ne]; exact tl.flatten_head_op
        · simpa only [Children.flatten, List.append_assoc] using heq
    | .infixN l w r, heq =>
        refine udLeadOp hG l b hb u (w.flatten ++ (r.flatten ++ s₁)) s₂ ?_ ?_ hs₂
        · rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
        · simpa only [Children.flatten, List.append_assoc] using heq
  termination_by sizeOf c + sizeOf u
end

/-- **The hard direction.** `Unambiguous G` implies `flatten` is injective on
`Expr G`. -/
theorem unambiguous_flatten_injective (hG : Unambiguous G) : FlattenInjective G := by
  intro e₁ e₂ he
  have heq : e₁.flatten ++ [] = e₂.flatten ++ [] := by simpa using he
  exact (udExpr hG e₁ e₂ [] [] heq (by intro o; simp) (by intro o; simp)).1

/-- If the grammar is unambiguous, `parse` yields at most one result: any two
expressions it returns are equal. (Immediate from completeness — both flatten to
`tkns`.) -/
theorem parse_unique (hG : FlattenInjective G) {tkns : List Token} {e₁ e₂ : Expr G}
    (h₁ : e₁ ∈ parse (G := G) tkns) (h₂ : e₂ ∈ parse (G := G) tkns) : e₁ = e₂ :=
  hG e₁ e₂ ((mem_parse_iff.mp h₁).trans (mem_parse_iff.mp h₂).symm)

end LambdaLab.Parser.Playground
