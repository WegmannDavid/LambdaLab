import LambdaLab.ParserOld.Playground2.Completeness

/-!
# Uniqueness: a syntactic criterion forcing `flatten` to be injective

`flatten` maps a parse tree to its token stream. A grammar is *unambiguous* when
`flatten` is injective on top-level expressions (`Tree G .loosest`). This file
proves a checkable syntactic criterion `Unambiguous G` (distinct name tokens +
forest-shaped precedence) implies `FlattenInjective G`.

The proof is a mutual prefix-form unique-decomposition over the whole tree
family. It works because `Tree.lean` keeps **every operand strictly tighter**
than its operator: an operator's separator token lives at the operator's own
(looser) level, so by acyclicity it can never sit at a top-level operand
boundary of any operand. The `Stops` predicate captures exactly this — "the
leftover after a tree does not begin with a token that could continue it" — and
is what makes the prefix-form generalization *true* (it is false without it:
`x` is a prefix of `x + y`).

Because the three former tree families (`Tree`/`TreeBelow`/`Expr`) are now one
`Level`-indexed `Tree`, `udTree` is *one* theorem over `Tree G l`, with the
right `Stops` flavour selected by `Level.stops l`.
-/

set_option maxHeartbeats 1000000

namespace LambdaLab.ParserOld.Playground2

open LambdaLab.ParserOld

variable {G : Grammar}

/-- A grammar is **unambiguous** when `flatten` is injective on top-level
expressions: no two distinct trees flatten to the same token string. -/
def FlattenInjective (G : Grammar) : Prop :=
  ∀ e₁ e₂ : Tree G .loosest, e₁.flatten = e₂.flatten → e₁ = e₂

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

/-- No cycle, transitive form: a strictly-tighter `c` cannot reach back to `a`. -/
theorem Tighter.irrefl_tighterEq {a c : G.Op} (h : Tighter G.tighter a c)
    (h' : TighterEq G.tighter c a) : False := by
  obtain ⟨b, hb, hbc⟩ := h.split
  exact no_cycle hb (hbc.trans h')

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
  theorem Tree.flatten_ne {l : Level G} (t : Tree G l) : t.flatten ≠ [] := by
    match t with
    | .op _ _ ch => simpa only [Tree.flatten] using ch.flatten_ne

  theorem Children.flatten_ne {b : G.Op} {s : Shape} (ch : Children G b s) :
      ch.flatten ≠ [] := by
    match ch with
    | .wLast _ => simp [Children.flatten]
    | .wCons _ _ _ => simp [Children.flatten]
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
    | .psLast w tb =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .psMore w ps =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .ptLast w => simpa only [Children.flatten] using w.flatten_ne
    | .ptCons w t =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .itLast w tb =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .itCons w tb t =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
end

/-! ## Leading-token facts -/

theorem Children.headWeave {parts : List Token} (w : Children G a (.weave parts)) :
    w.flatten.head? = parts.head? := by
  match w with
  | .wLast tk => rfl
  | .wCons tk e w => rfl

theorem Children.headOpWeave {a : G.Op} (w : Children G a (.weave (G.operator a).nameParts)) :
    w.flatten.head? = some (G.operator a).head := by
  rw [Children.headWeave, List.head?_eq_some_head (G.operator a).nameParts_ne]; rfl

theorem Children.headMemWeave {parts : List Token} (w : Children G a (.weave parts)) {t : Token}
    (ht : w.flatten.head? = some t) : t ∈ parts := by
  rw [Children.headWeave] at ht
  cases parts with
  | nil => simp at ht
  | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at ht
      subst ht; simp

theorem Children.headOpPrefix {a : G.Op} (p : Children G a .prefix) :
    p.flatten.head? = some (G.operator a).head := by
  cases p with
  | psLast w tb =>
      simp only [Children.flatten]; rw [head?_append_left w.flatten_ne]; exact w.headOpWeave
  | psMore w ps =>
      simp only [Children.flatten]; rw [head?_append_left w.flatten_ne]; exact w.headOpWeave

theorem Children.headOpPostTail {a : G.Op} (p : Children G a .postTail) :
    p.flatten.head? = some (G.operator a).head := by
  cases p with
  | ptLast w => simpa only [Children.flatten] using w.headOpWeave
  | ptCons w t =>
      simp only [Children.flatten]; rw [head?_append_left w.flatten_ne]; exact w.headOpWeave

theorem Children.headOpInfixTail {a : G.Op} (p : Children G a .infixTail) :
    p.flatten.head? = some (G.operator a).head := by
  cases p with
  | itLast w tb =>
      simp only [Children.flatten]; rw [head?_append_left w.flatten_ne]; exact w.headOpWeave
  | itCons w tb t =>
      simp only [Children.flatten, List.append_assoc]
      rw [head?_append_left w.flatten_ne]; exact w.headOpWeave

mutual
  theorem Tree.headTok_reach {l : Level G} (t : Tree G l) :
      ∃ o, t.flatten.head? = some (G.operator o).head ∧ Level.reaches l o := by
    match t with
    | .op a hc ch =>
        obtain ⟨o, hr, hh⟩ := ch.headTok_reach
        exact ⟨o, by simpa only [Tree.flatten] using hh, a, hc, hr⟩

  theorem Children.headTok_reach {a : G.Op} {f : Fixity} (ch : Children G a (.body f)) :
      ∃ o, TighterEq G.tighter a o ∧ ch.flatten.head? = some (G.operator o).head := by
    match ch with
    | .closed w =>
        exact ⟨a, TighterEq.refl, by simpa only [Children.flatten] using w.headOpWeave⟩
    | .«prefix» ps =>
        exact ⟨a, TighterEq.refl, by simpa only [Children.flatten] using ps.headOpPrefix⟩
    | .«postfix» tb pt =>
        obtain ⟨o, hh, x, hx, hxo⟩ := tb.headTok_reach
        refine ⟨o, (Tighter.trans_tighterEq (hx : Tighter G.tighter a x) hxo).toTighterEq, ?_⟩
        simp only [Children.flatten]; rw [head?_append_left tb.flatten_ne]; exact hh
    | .infixL hd tl =>
        obtain ⟨o, hh, x, hx, hxo⟩ := hd.headTok_reach
        refine ⟨o, (Tighter.trans_tighterEq (hx : Tighter G.tighter a x) hxo).toTighterEq, ?_⟩
        simp only [Children.flatten]; rw [head?_append_left hd.flatten_ne]; exact hh
    | .infixR hd tl =>
        obtain ⟨o, hh, x, hx, hxo⟩ := hd.headTok_reach
        refine ⟨o, (Tighter.trans_tighterEq (hx : Tighter G.tighter a x) hxo).toTighterEq, ?_⟩
        simp only [Children.flatten]; rw [head?_append_left hd.flatten_ne]; exact hh
    | .infixN l w r =>
        obtain ⟨o, hh, x, hx, hxo⟩ := l.headTok_reach
        refine ⟨o, (Tighter.trans_tighterEq (hx : Tighter G.tighter a x) hxo).toTighterEq, ?_⟩
        simp only [Children.flatten, List.append_assoc]
        rw [head?_append_left l.flatten_ne]; exact hh
end

/-- Specialisation of `Tree.headTok_reach` for `.tighterEq` trees. -/
theorem Tree.headTok_reachEq {b : G.Op} (u : Tree G (.tighterEq b)) :
    ∃ o, TighterEq G.tighter b o ∧ u.flatten.head? = some (G.operator o).head := by
  obtain ⟨o, hh, x, hx, hxo⟩ := u.headTok_reach
  exact ⟨o, (hx : TighterEq G.tighter b x).trans hxo, hh⟩

/-! ## The `Stops` predicate -/

/-- The leftover `s` does not begin with a token that could continue a tree at
level `a`: no operator reachable from `a` has its head there. (Vacuous when
`s = []`.) This is exactly what makes prefix-form unique decomposition true. -/
def Stops (a : G.Op) (s : List Token) : Prop :=
  ∀ o, TighterEq G.tighter a o → s.head? ≠ some (G.operator o).head

/-- `s` begins with no operator's head at all (stops every level). -/
def StopsAll (s : List Token) : Prop :=
  ∀ o : G.Op, s.head? ≠ some (G.operator o).head

/-- `s` stops every operator strictly tighter than `a` (what a `Tree G (.tighter a)`
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

/-- The `Stops` flavour appropriate to a level: `.tighter a` needs `StopsBelow a`,
`.tighterEq a` needs `Stops a`, `.loosest` needs `StopsAll`. -/
def Level.stops (l : Level G) (s : List Token) : Prop :=
  match l with
  | .tighter a   => StopsBelow a s
  | .tighterEq a => Stops a s
  | .loosest     => StopsAll (G := G) s

/-- A level-`Stops` hypothesis yields `Stops b` for any `b` satisfying the level. -/
theorem Level.stops.toStops {l : Level G} {s : List Token} (hs : Level.stops l s)
    {b : G.Op} (hb : Level.condition l b) : Stops b s := by
  cases l with
  | tighter a =>
      obtain ⟨c, hcm, hcb⟩ := (hb : Tighter G.tighter a b).split
      exact ((hs : StopsBelow a s) c hcm).mono hcb
  | tighterEq a => exact (hs : Stops a s).mono hb
  | loosest => exact (hs : StopsAll s).stops b

/-- A leftover beginning with `a`'s own head stops everything strictly tighter
than `a` (acyclicity: `a` is unreachable from anything tighter). -/
theorem StopsBelow_of_head (hG : Unambiguous G) {a : G.Op} {s : List Token}
    (h : s.head? = some (G.operator a).head) : StopsBelow a s := by
  intro b hb o hbo hcon
  rw [h] at hcon
  have heq : (G.operator a).head = (G.operator o).head := Option.some.inj hcon
  have hoa : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heq
  exact no_cycle hb (hoa ▸ hbo)

/-- A leftover beginning with `a`'s head stops a strictly-tighter `c`. -/
theorem Stops_of_head_tighter (hG : Unambiguous G) {a c : G.Op} (hac : Tighter G.tighter a c)
    {s : List Token} (h : s.head? = some (G.operator a).head) : Stops c s := by
  intro o hco hcon
  rw [h] at hcon
  have heq : (G.operator a).head = (G.operator o).head := Option.some.inj hcon
  have hao : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heq
  exact Tighter.irrefl_tighterEq hac (hao ▸ hco)

/-- A weave over the empty name-part list is uninhabited. -/
theorem Children.weave_not_nil {a : G.Op} (w : Children G a (.weave [])) : False := by cases w

/-- Constructor equality for `Tree.op` across an operator cast. The level
witness is proof-irrelevant, so only the operator and its children must match. -/
theorem Tree.op_cast_eq {l : Level G} {b₁ b₂ : G.Op} (hbb : b₁ = b₂)
    {h₁ : Level.condition l b₁} {h₂ : Level.condition l b₂}
    {ch₁ : Children G b₁ (.body (G.operator b₁).fixity)} {ch₂ : Children G b₂ (.body (G.operator b₂).fixity)}
    (hc : hbb ▸ ch₁ = ch₂) : Tree.op b₁ h₁ ch₁ = (Tree.op b₂ h₂ ch₂ : Tree G l) := by
  subst hbb; subst hc; rfl

/-- **Forest property.** Two nodes `b₁`, `b₂` reachable from a common `a` and both
reaching a common `o` are comparable. -/
theorem comparable_of_common (hG : Unambiguous G) {b₂ o : G.Op}
    (hb₂o : TighterEq G.tighter b₂ o) {a b₁ : G.Op}
    (hab₁ : TighterEq G.tighter a b₁) (hb₁o : TighterEq G.tighter b₁ o)
    (hab₂ : TighterEq G.tighter a b₂) :
    b₁ = b₂ ∨ Tighter G.tighter b₁ b₂ ∨ Tighter G.tighter b₂ b₁ := by
  revert hb₁o hab₂
  induction hab₁ with
  | @refl x =>
      intro hb₁o hab₂
      by_cases hbe : x = b₂
      · exact Or.inl hbe
      · exact Or.inr (Or.inl (hab₂.toTighter hbe))
  | @step x c b₁' hc h₁' ih =>
      intro hb₁o hab₂
      cases hab₂ with
      | refl =>
          by_cases hbe : b₁' = b₂
          · exact Or.inl hbe
          · exact Or.inr (Or.inr ((TighterEq.step hc h₁').toTighter (Ne.symm hbe)))
      | @step _ c₂ _ hc₂ h₂' =>
          by_cases hcc : c = c₂
          · subst hcc; exact ih hb₁o h₂'
          · exact (hG.tighter_disjoint x c c₂ hc hc₂ hcc o (h₁'.trans hb₁o) (h₂'.trans hb₂o)).elim

/-- The forest property at a level: two roots satisfying `l` that both reach a
common `o` are comparable. -/
theorem Level.comparable (hG : Unambiguous G) {l : Level G} {b₁ b₂ o : G.Op}
    (h₁ : Level.condition l b₁) (h₂ : Level.condition l b₂)
    (hb₁o : TighterEq G.tighter b₁ o) (hb₂o : TighterEq G.tighter b₂ o) :
    b₁ = b₂ ∨ Tighter G.tighter b₁ b₂ ∨ Tighter G.tighter b₂ b₁ := by
  cases l with
  | tighter a =>
      exact comparable_of_common hG hb₂o (h₁ : Tighter G.tighter a b₁).toTighterEq hb₁o
        (h₂ : Tighter G.tighter a b₂).toTighterEq
  | tighterEq a =>
      exact comparable_of_common hG hb₂o (h₁ : TighterEq G.tighter a b₁) hb₁o
        (h₂ : TighterEq G.tighter a b₂)
  | loosest =>
      obtain ⟨r₁, hr₁, ht₁⟩ := h₁
      obtain ⟨r₂, hr₂, ht₂⟩ := h₂
      by_cases hre : r₁ = r₂
      · subst hre
        exact comparable_of_common hG hb₂o ht₁ hb₁o ht₂
      · exact (hG.loosest_disjoint r₁ r₂ hr₁ hr₂ hre o (ht₁.trans hb₁o) (ht₂.trans hb₂o)).elim

theorem mem_of_mem_tail {α} {l : List α} {t : α} (h : t ∈ l.tail) : t ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp only [List.tail_cons] at h; exact List.mem_cons_of_mem x h

/-- Every level has positive `sizeOf` — needed to discharge `udTree`'s
termination measure when the level is an opaque variable. -/
theorem Level.sizeOf_pos (l : Level G) : 0 < sizeOf l := by
  cases l <;>
    simp only [Level.tighter.sizeOf_spec, Level.tighterEq.sizeOf_spec, Level.loosest.sizeOf_spec] <;>
    omega

/-! ## Mutual unique decomposition (prefix form, with `Stops`) -/

mutual
  theorem udTree (hG : Unambiguous G) {l : Level G} (t₁ t₂ : Tree G l) (s₁ s₂ : List Token)
      (h : t₁.flatten ++ s₁ = t₂.flatten ++ s₂) (hs₁ : Level.stops l s₁) (hs₂ : Level.stops l s₂) :
      t₁ = t₂ ∧ s₁ = s₂ := by
    match t₁, t₂ with
    | .op b₁ h₁ ch₁, .op b₂ h₂ ch₂ =>
        have heqc : ch₁.flatten ++ s₁ = ch₂.flatten ++ s₂ := by simpa only [Tree.flatten] using h
        by_cases hbb : b₁ = b₂
        · -- same top operator: compare children, witness irrelevant.
          have hsb₁ : Stops b₁ s₁ := hs₁.toStops h₁
          have hsb₂ : Stops b₂ s₂ := hs₂.toStops h₂
          have heqc' : (hbb ▸ ch₁).flatten ++ s₁ = ch₂.flatten ++ s₂ := by cases hbb; exact heqc
          have hc := udChildren hG (hbb ▸ ch₁) ch₂ s₁ s₂ heqc' (hbb ▸ hsb₁) hsb₂
          exact ⟨Tree.op_cast_eq hbb hc.1, hc.2⟩
        · -- cross-operator: shared leading op `o` is reached from both `b₁`, `b₂`;
          -- forest comparability reduces the strict side to `udOpNext`.
          obtain ⟨o₁, hr₁, hh₁⟩ := ch₁.headTok_reach
          obtain ⟨o₂, hr₂, hh₂⟩ := ch₂.headTok_reach
          have hhd : ch₁.flatten.head? = ch₂.flatten.head? :=
            head?_eq_of_prefix heqc ch₁.flatten_ne ch₂.flatten_ne
          rw [hh₁, hh₂] at hhd
          have hoo : o₁ = o₂ :=
            Classical.byContradiction fun hne => hG.heads_distinct hne (Option.some.inj hhd)
          subst hoo
          rcases Level.comparable hG h₁ h₂ hr₁ hr₂ with hbe | htb | htb
          · exact absurd hbe hbb
          · obtain ⟨b', hb', hb'b₂⟩ := htb.split
            exact (udOpNext hG ch₁ b' hb' (Tree.op b₂ hb'b₂ ch₂) s₁ s₂ heqc
              (hs₁.toStops h₁) (hs₂.toStops h₁)).elim
          · obtain ⟨b', hb', hb'b₁⟩ := htb.split
            exact (udOpNext hG ch₂ b' hb' (Tree.op b₁ hb'b₁ ch₁) s₂ s₁ heqc.symm
              (hs₂.toStops h₂) (hs₁.toStops h₂)).elim
  termination_by sizeOf t₁ + sizeOf t₂
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals (try simp only [Tree.op.sizeOf_spec, Level.tighter.sizeOf_spec, Level.tighterEq.sizeOf_spec, Level.loosest.sizeOf_spec])
    all_goals (try omega)
    all_goals (have hl := Level.sizeOf_pos l; omega)

  theorem udChildren (hG : Unambiguous G) {a : G.Op} {f : Fixity}
      (c₁ c₂ : Children G a (.body f)) (s₁ s₂ : List Token)
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
        have htb := udTree hG tb₁ tb₂ (pt₁.flatten ++ s₁) (pt₂.flatten ++ s₂) heq
          (StopsBelow_of_head hG (by rw [head?_append_left pt₁.flatten_ne]; exact pt₁.headOpPostTail))
          (StopsBelow_of_head hG (by rw [head?_append_left pt₂.flatten_ne]; exact pt₂.headOpPostTail))
        have hpt := udPostfixTail hG pt₁ pt₂ s₁ s₂ htb.2 hs₁ hs₂
        exact ⟨by rw [htb.1, hpt.1], hpt.2⟩
    | .infixL hd₁ tl₁, .infixL hd₂ tl₂ =>
        have heq : hd₁.flatten ++ (tl₁.flatten ++ s₁) = hd₂.flatten ++ (tl₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hhd := udTree hG hd₁ hd₂ (tl₁.flatten ++ s₁) (tl₂.flatten ++ s₂) heq
          (StopsBelow_of_head hG (by rw [head?_append_left tl₁.flatten_ne]; exact tl₁.headOpInfixTail))
          (StopsBelow_of_head hG (by rw [head?_append_left tl₂.flatten_ne]; exact tl₂.headOpInfixTail))
        have htl := udInfixTail hG tl₁ tl₂ s₁ s₂ hhd.2 hs₁ hs₂
        exact ⟨by rw [hhd.1, htl.1], htl.2⟩
    | .infixR hd₁ tl₁, .infixR hd₂ tl₂ =>
        have heq : hd₁.flatten ++ (tl₁.flatten ++ s₁) = hd₂.flatten ++ (tl₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hhd := udTree hG hd₁ hd₂ (tl₁.flatten ++ s₁) (tl₂.flatten ++ s₂) heq
          (StopsBelow_of_head hG (by rw [head?_append_left tl₁.flatten_ne]; exact tl₁.headOpInfixTail))
          (StopsBelow_of_head hG (by rw [head?_append_left tl₂.flatten_ne]; exact tl₂.headOpInfixTail))
        have htl := udInfixTail hG tl₁ tl₂ s₁ s₂ hhd.2 hs₁ hs₂
        exact ⟨by rw [hhd.1, htl.1], htl.2⟩
    | .infixN l₁ w₁ r₁, .infixN l₂ w₂ r₂ =>
        have heq : l₁.flatten ++ (w₁.flatten ++ (r₁.flatten ++ s₁))
                 = l₂.flatten ++ (w₂.flatten ++ (r₂.flatten ++ s₂)) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hl := udTree hG l₁ l₂ (w₁.flatten ++ (r₁.flatten ++ s₁))
          (w₂.flatten ++ (r₂.flatten ++ s₂)) heq
          (StopsBelow_of_head hG (by rw [head?_append_left w₁.flatten_ne]; exact w₁.headOpWeave))
          (StopsBelow_of_head hG (by rw [head?_append_left w₂.flatten_ne]; exact w₂.headOpWeave))
        have hw := udWoven hG w₁ w₂ (r₁.flatten ++ s₁) (r₂.flatten ++ s₂) hl.2
          (nameParts_tail_notHead hG a)
        have hr := udTree hG r₁ r₂ s₁ s₂ hw.2 hs₁.below hs₂.below
        exact ⟨by rw [hl.1, hw.1, hr.1], hr.2⟩
  termination_by sizeOf c₁ + sizeOf c₂

  theorem udPrefixStack (hG : Unambiguous G) {a : G.Op} (p₁ p₂ : Children G a .prefix)
      (s₁ s₂ : List Token) (h : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    match p₁, p₂ with
    | .psLast w₁ tb₁, .psLast w₂ tb₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁) = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have htb := udTree hG tb₁ tb₂ s₁ s₂ hw.2 hs₁.below hs₂.below
        exact ⟨by rw [hw.1, htb.1], htb.2⟩
    | .psLast w₁ tb₁, .psMore w₂ p₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁) = w₂.flatten ++ (p₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (p₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        -- tb₁ leads with a tighter operator's head; p₂ leads with a.head — contradiction.
        obtain ⟨o, hhead, x, hxc, hxo⟩ := tb₁.headTok_reach
        have hhd : tb₁.flatten.head? = p₂.flatten.head? :=
          head?_eq_of_prefix hw.2 tb₁.flatten_ne p₂.flatten_ne
        rw [p₂.headOpPrefix, hhead] at hhd
        have heq2 : (G.operator o).head = (G.operator a).head := Option.some.inj hhd
        have hoa : o = a := Classical.byContradiction fun hne => hG.heads_distinct hne heq2
        exact (Tighter.irrefl_tighterEq (hxc : Tighter G.tighter a x) (hoa ▸ hxo)).elim
    | .psMore w₁ p₁, .psLast w₂ tb₂ =>
        have heq : w₁.flatten ++ (p₁.flatten ++ s₁) = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (p₁.flatten ++ s₁) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        obtain ⟨o, hhead, x, hxc, hxo⟩ := tb₂.headTok_reach
        have hhd : p₁.flatten.head? = tb₂.flatten.head? :=
          head?_eq_of_prefix hw.2 p₁.flatten_ne tb₂.flatten_ne
        rw [p₁.headOpPrefix, hhead] at hhd
        have heq2 : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
        have hoa : o = a := Classical.byContradiction fun hne => hG.heads_distinct hne heq2.symm
        exact (Tighter.irrefl_tighterEq (hxc : Tighter G.tighter a x) (hoa ▸ hxo)).elim
    | .psMore w₁ p₁, .psMore w₂ p₂ =>
        have heq : w₁.flatten ++ (p₁.flatten ++ s₁) = w₂.flatten ++ (p₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (p₁.flatten ++ s₁) (p₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have hp := udPrefixStack hG p₁ p₂ s₁ s₂ hw.2 hs₁ hs₂
        exact ⟨by rw [hw.1, hp.1], hp.2⟩
  termination_by sizeOf p₁ + sizeOf p₂

  theorem udPostfixTail (hG : Unambiguous G) {a : G.Op} (p₁ p₂ : Children G a .postTail)
      (s₁ s₂ : List Token) (h : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    match p₁, p₂ with
    | .ptLast w₁, .ptLast w₂ =>
        have heq : w₁.flatten ++ s₁ = w₂.flatten ++ s₂ := by
          simpa only [Children.flatten] using h
        have hw := udWoven hG w₁ w₂ s₁ s₂ heq (nameParts_tail_notHead hG a)
        exact ⟨by rw [hw.1], hw.2⟩
    | .ptLast w₁, .ptCons w₂ t₂ =>
        have heq : w₁.flatten ++ s₁ = w₂.flatten ++ (t₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ s₁ (t₂.flatten ++ s₂) heq (nameParts_tail_notHead hG a)
        exact absurd (by rw [hw.2, head?_append_left t₂.flatten_ne]; exact t₂.headOpPostTail)
          (hs₁ a TighterEq.refl)
    | .ptCons w₁ t₁, .ptLast w₂ =>
        have heq : w₁.flatten ++ (t₁.flatten ++ s₁) = w₂.flatten ++ s₂ := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (t₁.flatten ++ s₁) s₂ heq (nameParts_tail_notHead hG a)
        exact absurd (by rw [← hw.2, head?_append_left t₁.flatten_ne]; exact t₁.headOpPostTail)
          (hs₂ a TighterEq.refl)
    | .ptCons w₁ t₁, .ptCons w₂ t₂ =>
        have heq : w₁.flatten ++ (t₁.flatten ++ s₁) = w₂.flatten ++ (t₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (t₁.flatten ++ s₁) (t₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have ht := udPostfixTail hG t₁ t₂ s₁ s₂ hw.2 hs₁ hs₂
        exact ⟨by rw [hw.1, ht.1], ht.2⟩
  termination_by sizeOf p₁ + sizeOf p₂

  theorem udInfixTail (hG : Unambiguous G) {a : G.Op} (p₁ p₂ : Children G a .infixTail)
      (s₁ s₂ : List Token) (h : p₁.flatten ++ s₁ = p₂.flatten ++ s₂)
      (hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
    match p₁, p₂ with
    | .itLast w₁ tb₁, .itLast w₂ tb₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁) = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have htb := udTree hG tb₁ tb₂ s₁ s₂ hw.2 hs₁.below hs₂.below
        exact ⟨by rw [hw.1, htb.1], htb.2⟩
    | .itLast w₁ tb₁, .itCons w₂ tb₂ t₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ s₁)
                 = w₂.flatten ++ (tb₂.flatten ++ (t₂.flatten ++ s₂)) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ s₁) (tb₂.flatten ++ (t₂.flatten ++ s₂)) heq
          (nameParts_tail_notHead hG a)
        have htb := udTree hG tb₁ tb₂ s₁ (t₂.flatten ++ s₂) hw.2 hs₁.below
          (StopsBelow_of_head hG (by rw [head?_append_left t₂.flatten_ne]; exact t₂.headOpInfixTail))
        exact absurd (by rw [htb.2, head?_append_left t₂.flatten_ne]; exact t₂.headOpInfixTail)
          (hs₁ a TighterEq.refl)
    | .itCons w₁ tb₁ t₁, .itLast w₂ tb₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ (t₁.flatten ++ s₁))
                 = w₂.flatten ++ (tb₂.flatten ++ s₂) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ (t₁.flatten ++ s₁)) (tb₂.flatten ++ s₂) heq
          (nameParts_tail_notHead hG a)
        have htb := udTree hG tb₁ tb₂ (t₁.flatten ++ s₁) s₂ hw.2
          (StopsBelow_of_head hG (by rw [head?_append_left t₁.flatten_ne]; exact t₁.headOpInfixTail))
          hs₂.below
        exact absurd (by rw [← htb.2, head?_append_left t₁.flatten_ne]; exact t₁.headOpInfixTail)
          (hs₂ a TighterEq.refl)
    | .itCons w₁ tb₁ t₁, .itCons w₂ tb₂ t₂ =>
        have heq : w₁.flatten ++ (tb₁.flatten ++ (t₁.flatten ++ s₁))
                 = w₂.flatten ++ (tb₂.flatten ++ (t₂.flatten ++ s₂)) := by
          simpa only [Children.flatten, List.append_assoc] using h
        have hw := udWoven hG w₁ w₂ (tb₁.flatten ++ (t₁.flatten ++ s₁))
          (tb₂.flatten ++ (t₂.flatten ++ s₂)) heq (nameParts_tail_notHead hG a)
        have htb := udTree hG tb₁ tb₂ (t₁.flatten ++ s₁) (t₂.flatten ++ s₂) hw.2
          (StopsBelow_of_head hG (by rw [head?_append_left t₁.flatten_ne]; exact t₁.headOpInfixTail))
          (StopsBelow_of_head hG (by rw [head?_append_left t₂.flatten_ne]; exact t₂.headOpInfixTail))
        have ht := udInfixTail hG t₁ t₂ s₁ s₂ htb.2 hs₁ hs₂
        exact ⟨by rw [hw.1, htb.1, ht.1], ht.2⟩
  termination_by sizeOf p₁ + sizeOf p₂

  theorem udWoven (hG : Unambiguous G) {a : G.Op} {parts : List Token}
      (w₁ w₂ : Children G a (.weave parts)) (s₁ s₂ : List Token)
      (h : w₁.flatten ++ s₁ = w₂.flatten ++ s₂)
      (hpr : ∀ tk ∈ parts.tail, ∀ o : G.Op, (G.operator o).head ≠ tk) :
      w₁ = w₂ ∧ s₁ = s₂ := by
    match w₁, w₂ with
    | .wLast tk, w₂ =>
        cases w₂ with
        | wLast tk' =>
            refine ⟨rfl, ?_⟩
            simpa only [Children.flatten, List.cons_append, List.nil_append,
              List.cons.injEq, true_and] using h
        | wCons tk' e w => exact (w.weave_not_nil).elim
    | .wCons tk e₁ w₁', w₂ =>
        cases w₂ with
        | wLast tk' => exact (w₁'.weave_not_nil).elim
        | wCons _ e₂ w₂' =>
        have heq : e₁.flatten ++ (w₁'.flatten ++ s₁) = e₂.flatten ++ (w₂'.flatten ++ s₂) := by
          have h' : [tk] ++ (e₁.flatten ++ (w₁'.flatten ++ s₁))
                  = [tk] ++ (e₂.flatten ++ (w₂'.flatten ++ s₂)) := by
            simpa only [Children.flatten, List.append_assoc] using h
          exact List.append_cancel_left h'
        -- each interior hole is followed by the next name-part, which is nobody's head
        have hstop1 : StopsAll (G := G) (w₁'.flatten ++ s₁) := by
          intro o hcon
          rw [head?_append_left w₁'.flatten_ne] at hcon
          exact hpr _ (w₁'.headMemWeave hcon) o rfl
        have hstop2 : StopsAll (G := G) (w₂'.flatten ++ s₂) := by
          intro o hcon
          rw [head?_append_left w₂'.flatten_ne] at hcon
          exact hpr _ (w₂'.headMemWeave hcon) o rfl
        have hrec := udTree hG e₁ e₂ (w₁'.flatten ++ s₁) (w₂'.flatten ++ s₂) heq hstop1 hstop2
        have hrec2 := udWoven hG w₁' w₂' s₁ s₂ hrec.2 (fun t ht => hpr t (mem_of_mem_tail ht))
        exact ⟨by rw [hrec.1, hrec2.1], hrec2.2⟩
  termination_by sizeOf w₁ + sizeOf w₂

  /-- The leading-operand argument for the infix/postfix `op`-vs-tighter cases.
  `tb` is the leading operand (strictly tighter than `a`); `mid` begins with `a`'s
  separator head; `u` is a tighter tree. Forest comparability of the two leading
  operators yields the contradiction. -/
  theorem udLeadOp (hG : Unambiguous G) {a : G.Op} (tb : Tree G (.tighter a))
      (b : G.Op) (hb : b ∈ G.tighter a) (u : Tree G (.tighterEq b)) (mid s₂ : List Token)
      (hmid : mid.head? = some (G.operator a).head)
      (hlt : tb.flatten ++ mid = u.flatten ++ s₂) (hs₂ : Stops a s₂) : False := by
    match tb, u with
    | .op c hac chc, .op d hbd chd =>
        have hlt' : chc.flatten ++ mid = chd.flatten ++ s₂ := by simpa only [Tree.flatten] using hlt
        obtain ⟨o₁, hco, hh₁⟩ := chc.headTok_reach
        obtain ⟨o₂, hdo, hh₂⟩ := chd.headTok_reach
        have hhd : chc.flatten.head? = chd.flatten.head? :=
          head?_eq_of_prefix hlt' chc.flatten_ne chd.flatten_ne
        rw [hh₁, hh₂] at hhd
        have hoo : o₁ = o₂ :=
          Classical.byContradiction fun hne => hG.heads_distinct hne (Option.some.inj hhd)
        subst hoo
        have had : Tighter G.tighter a d := tighter_of_mem_tighterEq hb (hbd : TighterEq G.tighter b d)
        rcases comparable_of_common hG hdo (hac : Tighter G.tighter a c).toTighterEq hco had.toTighterEq
          with hcd | hcd | hcd
        · -- c = d: same leading operator → children equal → mid = s₂, contradicting hmid/hs₂.
          have hsmid : Stops c mid := Stops_of_head_tighter hG (hac : Tighter G.tighter a c) hmid
          have heqc' : (hcd ▸ chc).flatten ++ mid = chd.flatten ++ s₂ := by cases hcd; exact hlt'
          have hrec := udChildren hG (hcd ▸ chc) chd mid s₂ heqc'
            (hcd ▸ hsmid) (hs₂.mono had.toTighterEq)
          exact hs₂ a TighterEq.refl (by rw [← hrec.2]; exact hmid)
        · obtain ⟨c', hc', hc'd⟩ := hcd.split
          exact udOpNext hG chc c' hc' (Tree.op d hc'd chd) mid s₂ hlt'
            (Stops_of_head_tighter hG (hac : Tighter G.tighter a c) hmid) (hs₂.mono hac.toTighterEq)
        · obtain ⟨d', hd', hd'c⟩ := hcd.split
          exact udOpNext hG chd d' hd' (Tree.op c hd'c chc) s₂ mid hlt'.symm
            (hs₂.mono had.toTighterEq) (Stops_of_head_tighter hG had hmid)
  termination_by sizeOf tb + sizeOf u
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals (try simp only [Tree.op.sizeOf_spec, Level.tighter.sizeOf_spec, Level.tighterEq.sizeOf_spec, Level.loosest.sizeOf_spec])
    all_goals omega

  theorem udOpNext (hG : Unambiguous G) {a : G.Op} {f : Fixity}
      (c : Children G a (.body f))
      (b : G.Op) (hb : b ∈ G.tighter a) (u : Tree G (.tighterEq b)) (s₁ s₂ : List Token)
      (heq : c.flatten ++ s₁ = u.flatten ++ s₂)
      (_hs₁ : Stops a s₁) (hs₂ : Stops a s₂) : False := by
    match c, heq with
    | .closed w, heq =>
        obtain ⟨o, hr, hh⟩ := u.headTok_reachEq
        have hca : (Children.closed w).flatten.head? = some (G.operator a).head := by
          simpa only [Children.flatten] using w.headOpWeave
        have hhd : (Children.closed w).flatten.head? = u.flatten.head? :=
          head?_eq_of_prefix heq (Children.closed w).flatten_ne u.flatten_ne
        rw [hca, hh] at hhd
        have heads : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
        have hoa : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heads
        exact no_cycle hb (hoa ▸ hr)
    | .«prefix» ps, heq =>
        obtain ⟨o, hr, hh⟩ := u.headTok_reachEq
        have hca : (Children.«prefix» ps).flatten.head? = some (G.operator a).head := by
          simpa only [Children.flatten] using ps.headOpPrefix
        have hhd : (Children.«prefix» ps).flatten.head? = u.flatten.head? :=
          head?_eq_of_prefix heq (Children.«prefix» ps).flatten_ne u.flatten_ne
        rw [hca, hh] at hhd
        have heads : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
        have hoa : a = o := Classical.byContradiction fun hne => hG.heads_distinct hne heads
        exact no_cycle hb (hoa ▸ hr)
    | .«postfix» tb pt, heq =>
        refine udLeadOp hG tb b hb u (pt.flatten ++ s₁) s₂ ?_ ?_ hs₂
        · rw [head?_append_left pt.flatten_ne]; exact pt.headOpPostTail
        · simpa only [Children.flatten, List.append_assoc] using heq
    | .infixL hd tl, heq =>
        refine udLeadOp hG hd b hb u (tl.flatten ++ s₁) s₂ ?_ ?_ hs₂
        · rw [head?_append_left tl.flatten_ne]; exact tl.headOpInfixTail
        · simpa only [Children.flatten, List.append_assoc] using heq
    | .infixR hd tl, heq =>
        refine udLeadOp hG hd b hb u (tl.flatten ++ s₁) s₂ ?_ ?_ hs₂
        · rw [head?_append_left tl.flatten_ne]; exact tl.headOpInfixTail
        · simpa only [Children.flatten, List.append_assoc] using heq
    | .infixN l w r, heq =>
        refine udLeadOp hG l b hb u (w.flatten ++ (r.flatten ++ s₁)) s₂ ?_ ?_ hs₂
        · rw [head?_append_left w.flatten_ne]; exact w.headOpWeave
        · simpa only [Children.flatten, List.append_assoc] using heq
  termination_by sizeOf c + sizeOf u
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals (try simp only [Tree.op.sizeOf_spec, Level.tighter.sizeOf_spec, Level.tighterEq.sizeOf_spec, Level.loosest.sizeOf_spec])
    all_goals omega
end

/-- **The hard direction.** `Unambiguous G` implies `flatten` is injective on
`Tree G .loosest`. -/
theorem unambiguous_flatten_injective (hG : Unambiguous G) : FlattenInjective G := by
  intro e₁ e₂ he
  have heq : e₁.flatten ++ [] = e₂.flatten ++ [] := by simpa using he
  exact (udTree hG e₁ e₂ [] [] heq (by intro o; simp) (by intro o; simp)).1

/-- If the grammar is unambiguous, `parse` yields at most one result: any two
expressions it returns are equal. -/
theorem parse_unique (hG : FlattenInjective G) {tkns : List Token} {e₁ e₂ : Tree G .loosest}
    (h₁ : e₁ ∈ parse (G := G) tkns) (h₂ : e₂ ∈ parse (G := G) tkns) : e₁ = e₂ :=
  hG e₁ e₂ ((mem_parse_iff.mp h₁).trans (mem_parse_iff.mp h₂).symm)

end LambdaLab.ParserOld.Playground2
