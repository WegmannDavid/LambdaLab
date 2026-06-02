import LambdaLab.Parser.Playground.Completeness

/-!
# Uniqueness: when does `parse` return at most one result?

`parse` returns a *list* of all full parses. It returns "at most one result"
(all returned expressions are equal) **iff** the grammar is unambiguous, i.e.
`flatten` is injective on `Expr G`. That equivalence has a cheap half and a
hard half:

* **Cheap (`parse_unique`)**: `FlattenInjective G → parse` is subsingleton.
  Immediate from soundness — the parser invents no parse beyond the genuine
  tree ambiguity, so two results have equal flatten, hence are equal.
* **Hard (`unambiguous_flatten_injective`)**: a *checkable syntactic* criterion
  `Unambiguous G` (distinct name tokens + forest-shaped precedence) implies
  `FlattenInjective G`. This is the substantial direction (mutual tree
  induction); the concrete grammars then discharge `Unambiguous` by `cases`.
-/

namespace LambdaLab.Parser.Playground

open LambdaLab.Parser

variable {G : Grammar}

/-- A grammar is **unambiguous** when `flatten` is injective on top-level
expressions: no two distinct trees flatten to the same token string. -/
def FlattenInjective (G : Grammar) : Prop :=
  ∀ e₁ e₂ : Expr G, e₁.flatten = e₂.flatten → e₁ = e₂

/-- If the grammar is unambiguous, `parse` yields at most one result: any two
expressions it returns are equal. (Immediate from soundness — both flatten to
`tkns`.) -/
theorem parse_unique (hG : FlattenInjective G) {tkns : List Token} {e₁ e₂ : Expr G}
    (h₁ : e₁ ∈ parse (G := G) tkns) (h₂ : e₂ ∈ parse (G := G) tkns) : e₁ = e₂ :=
  hG e₁ e₂ ((mem_parse_iff.mp h₁).trans (mem_parse_iff.mp h₂).symm)

/-! ## A checkable sufficient criterion for unambiguity

`Unambiguous G` bundles the two syntactic conditions that rule out all three
ambiguity sources:

* distinct name tokens (`nameParts_nodup` + `nameParts_disjoint`) — handles the
  intra-operator split and the operator-vs-fall-through cases;
* forest-shaped precedence (`tighter_disjoint` + `loosest_disjoint`: distinct
  immediate-tighter siblings, and distinct roots, have disjoint reachable sets)
  — handles the fall-through *path* (diamond) and multi-root cases.

It is decidable on a concrete grammar (`cases` on `Op`), strictly more general
than requiring a total order (it admits `arith`'s branching `mul → {paren,num}`),
and sufficient for `FlattenInjective`. -/
structure Unambiguous (G : Grammar) : Prop where
  nameParts_nodup : ∀ a : G.Op, (G.operator a).nameParts.Nodup
  nameParts_disjoint : ∀ a b : G.Op, a ≠ b →
    ∀ tk ∈ (G.operator a).nameParts, tk ∉ (G.operator b).nameParts
  tighter_disjoint : ∀ (a b₁ b₂ : G.Op), b₁ ∈ G.tighter a → b₂ ∈ G.tighter a → b₁ ≠ b₂ →
    ∀ c, ReachTighter G.tighter b₁ c → ReachTighter G.tighter b₂ c → False
  loosest_disjoint : ∀ (r₁ r₂ : G.Op), r₁ ∈ G.loosest → r₂ ∈ G.loosest → r₁ ≠ r₂ →
    ∀ c, ReachTighter G.tighter r₁ c → ReachTighter G.tighter r₂ c → False

/-- A sink (`tighter a = []`) reaches only itself — inverting `ReachTighter`. -/
theorem ReachTighter.eq_of_sink {t : G.Op → List G.Op} {a c : G.Op}
    (hsink : t a = []) (h : ReachTighter t a c) : c = a := by
  cases h with
  | refl => rfl
  | step hmem _ => rw [hsink] at hmem; exact absurd hmem List.not_mem_nil

/-- `ReachTighter` is transitive — composing two tighter-paths. -/
theorem ReachTighter.trans {t : G.Op → List G.Op} {a b c : G.Op}
    (h₁ : ReachTighter t a b) (h₂ : ReachTighter t b c) : ReachTighter t a c := by
  induction h₁ with
  | refl => exact h₂
  | step hmem _ ih => exact ReachTighter.step hmem (ih h₂)

/-! ## Structural building blocks for `unambiguous_flatten_injective`

These mutual structural lemmas hold for *any* grammar and are the scaffolding the
hard direction is built on. `*_flatten_ne` (flatten is never empty) is needed to
land the leading-token argument; it is fully proved. -/

mutual
  /-- A `Tree`'s flatten is never empty. -/
  theorem Tree.flatten_ne {b : G.Op} (t : Tree G b) : t.flatten ≠ [] := by
    match t with
    | .op _ ch => simpa only [Tree.flatten] using ch.flatten_ne
    | .next tb => simpa only [Tree.flatten] using tb.flatten_ne

  /-- A `TreeBelow`'s flatten is never empty. -/
  theorem TreeBelow.flatten_ne {b : G.Op} (t : TreeBelow G b) : t.flatten ≠ [] := by
    match t with
    | .mk _ _ tc => simpa only [TreeBelow.flatten] using tc.flatten_ne

  /-- A `Children`'s flatten is never empty (the operator's name-parts are
  non-empty, so even a `closed` node emits at least one token). -/
  theorem Children.flatten_ne {b : G.Op} {f : Fixity} (ch : Children G b f) :
      ch.flatten ≠ [] := by
    match ch with
    | .closed w => simpa only [Children.flatten] using w.flatten_ne
    | .prefix w _ =>
        simp only [Children.flatten]; intro h
        exact w.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .postfix t _ =>
        simp only [Children.flatten]; intro h
        exact t.flatten_ne (List.append_eq_nil_iff.mp h).1
    | .infixL l _ _ =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
    | .infixR l _ _ =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
    | .infixN l _ _ =>
        simp only [Children.flatten]; intro h
        exact l.flatten_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1

  /-- A `Woven`'s flatten is never empty. -/
  theorem Woven.flatten_ne {parts : List Token} (w : Woven G parts) : w.flatten ≠ [] := by
    match w with
    | .last _ => simp [Woven.flatten]
    | .cons _ _ _ => simp [Woven.flatten]
end

/-- An operator's head token is one of its name-parts. -/
theorem Operator.head_mem (o : Operator) : o.head ∈ o.nameParts :=
  List.head_mem o.nameParts_ne

/-- Distinct operators have distinct head tokens (from `nameParts_disjoint`). -/
theorem Unambiguous.heads_distinct (hG : Unambiguous G) {o o' : G.Op} (h : o ≠ o') :
    (G.operator o).head ≠ (G.operator o').head := by
  intro he
  have h1 : (G.operator o).head ∈ (G.operator o).nameParts := Operator.head_mem _
  have h2 : (G.operator o').head ∈ (G.operator o').nameParts := Operator.head_mem _
  rw [← he] at h2
  exact hG.nameParts_disjoint o o' h _ h1 h2

/-! ## Step 1: head-token facts -/

theorem Woven.flatten_head {parts : List Token} (w : Woven G parts) :
    w.flatten.head? = parts.head? := by
  match w with
  | .last tk => rfl
  | .cons tk e w => rfl

/-- The head of a `Woven (G.operator a).nameParts` flatten is `(G.operator a).head`. -/
theorem Woven.flatten_head_op {a : G.Op} (w : Woven G (G.operator a).nameParts) :
    w.flatten.head? = some (G.operator a).head := by
  rw [Woven.flatten_head]
  rw [List.head?_eq_some_head (G.operator a).nameParts_ne]
  rfl

/-- helper: head? of `l ++ s` is `l.head?` when `l ≠ []`. -/
theorem head?_append_left {l s : List Token} (h : l ≠ []) :
    (l ++ s).head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

/-! ## Step 1: leading-token reachability -/

mutual
  theorem Tree.headTok_reach {b : G.Op} (t : Tree G b) :
      ∃ o, ReachTighter G.tighter b o ∧ t.flatten.head? = some (G.operator o).head := by
    match t with
    | .op a ch =>
        -- flatten = ch.flatten
        obtain ⟨o, hreach, hhead⟩ := ch.headTok_reach
        exact ⟨o, hreach, by simpa only [Tree.flatten] using hhead⟩
    | .next tb =>
        obtain ⟨o, hreach, hhead⟩ := tb.headTok_reach
        exact ⟨o, hreach, by simpa only [Tree.flatten] using hhead⟩

  theorem TreeBelow.headTok_reach {a : G.Op} (tb : TreeBelow G a) :
      ∃ o, ReachTighter G.tighter a o ∧ tb.flatten.head? = some (G.operator o).head := by
    match tb with
    | .mk b hmem t =>
        obtain ⟨o, hreach, hhead⟩ := t.headTok_reach
        exact ⟨o, ReachTighter.step hmem hreach, by simpa only [TreeBelow.flatten] using hhead⟩

  theorem Children.headTok_reach {a : G.Op} {f : Fixity} (ch : Children G a f) :
      ∃ o, ReachTighter G.tighter a o ∧ ch.flatten.head? = some (G.operator o).head := by
    match ch with
    | .closed w =>
        exact ⟨a, ReachTighter.refl, by simpa only [Children.flatten] using w.flatten_head_op⟩
    | .prefix w t =>
        refine ⟨a, ReachTighter.refl, ?_⟩
        simp only [Children.flatten]
        rw [head?_append_left w.flatten_ne]
        exact w.flatten_head_op
    | .postfix t w =>
        -- leading operand is t : Tree G a
        obtain ⟨o, hreach, hhead⟩ := t.headTok_reach
        refine ⟨o, hreach, ?_⟩
        simp only [Children.flatten]
        rw [head?_append_left t.flatten_ne]
        exact hhead
    | .infixL l w r =>
        -- leading operand l : Tree G a
        obtain ⟨o, hreach, hhead⟩ := l.headTok_reach
        refine ⟨o, hreach, ?_⟩
        simp only [Children.flatten]
        rw [List.append_assoc, head?_append_left l.flatten_ne]
        exact hhead
    | .infixR l w r =>
        -- leading operand l : TreeBelow G a
        obtain ⟨o, hreach, hhead⟩ := l.headTok_reach
        refine ⟨o, hreach, ?_⟩
        simp only [Children.flatten]
        rw [List.append_assoc, head?_append_left l.flatten_ne]
        exact hhead
    | .infixN l w r =>
        obtain ⟨o, hreach, hhead⟩ := l.headTok_reach
        refine ⟨o, hreach, ?_⟩
        simp only [Children.flatten]
        rw [List.append_assoc, head?_append_left l.flatten_ne]
        exact hhead
end

/-- Leading tokens agree across a prefix equation of two non-empty flattens. -/
theorem head?_eq_of_prefix {l₁ l₂ s₁ s₂ : List Token}
    (h : l₁ ++ s₁ = l₂ ++ s₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    l₁.head? = l₂.head? := by
  have : (l₁ ++ s₁).head? = (l₂ ++ s₂).head? := by rw [h]
  rwa [head?_append_left h₁, head?_append_left h₂] at this

/-! ## Step 3: acyclicity -/

/-- No cycle: if `b` is immediately tighter than `a`, then `a` is not reachable
from `b`. (From `tighter_wf`.) -/
theorem no_cycle {a b : G.Op} (h : b ∈ G.tighter a) :
    ¬ ReachTighter G.tighter b a := by
  -- General statement, proved by well-founded induction on the *endpoint*.
  suffices H : ∀ a, ∀ b, b ∈ G.tighter a → ReachTighter G.tighter b a → False from H a b h
  intro a
  induction a using G.tighter_wf.induction with
  | _ a ih =>
    intro b hRba hreach
    cases hreach with
    | refl => exact ih a hRba a hRba ReachTighter.refl
    | step hRcb hca =>
        rename_i c
        have hcb : ReachTighter G.tighter c b :=
          hca.trans (ReachTighter.step hRba ReachTighter.refl)
        exact ih b hRba c hRcb hcb

/-! ## Step 2: unique decomposition (prefix form), mutual over the tree family -/

/-- **CRUX (isolated `sorry`).** The leading-operand argument for the
infix/postfix `op`-vs-`next` case.

Setup: `lead : Tree G d` is the leading operand of an `op a _` node whose fixity
is infix or postfix, so `lead` sits at a level `d` with `ReachTighter a d` (either
`d = a`, for postfix/infixL, or `d` strictly tighter, for infixR/infixN). Right
after `lead` comes operator `a`'s separator weave, whose first token is
`(G.operator a).head` — hence `mid` (everything in `op a _`'s flatten after
`lead`, plus the outer leftover `s₁`) begins with `(G.operator a).head`.

This is compared against a strictly-tighter `u : Tree G b` (`b ∈ tighter a`):
`lead.flatten ++ mid = u.flatten ++ s₂`.

**Why it is false (the open argument).** `(G.operator a).head` occurs here at a
*top-level* position of `op a _` (right after a complete operand `lead`). In
`u : Tree G b`, with `a` unreachable from `b` (acyclicity), the token
`(G.operator a).head` — a name-part of `a` — can occur only *inside a delimited
interior hole* (an `Expr` between two name-parts of some operator reachable from
`b`), never at top level after a complete operand boundary. Forcing the operand
boundary `lead` to coincide with a top-level boundary of `u` and deriving the
contradiction needs a positional / "top-level token" invariant on `flatten`,
which is not yet developed here. -/
theorem crux_infixPostfix (hG : Unambiguous G) {a b d : G.Op}
    (hb : b ∈ G.tighter a) (had : ReachTighter G.tighter a d)
    (lead : Tree G d) (u : Tree G b) (mid s₂ : List Token)
    (hmid : mid.head? = some (G.operator a).head)
    (h : lead.flatten ++ mid = u.flatten ++ s₂) : False := by
  sorry

theorem udOpNext (hG : Unambiguous G) {a : G.Op}
    (c : Children G a (G.operator a).fixity)
    (b : G.Op) (hb : b ∈ G.tighter a) (u : Tree G b) (s₁ s₂ : List Token)
    (h : (Tree.op a c).flatten ++ s₁ = (Tree.next (.mk b hb u)).flatten ++ s₂) :
    False := by
  have heq : c.flatten ++ s₁ = u.flatten ++ s₂ := by
    simpa only [Tree.flatten, TreeBelow.flatten] using h
  obtain ⟨o, hr, hh⟩ := u.headTok_reach
  have hhd : c.flatten.head? = u.flatten.head? :=
    head?_eq_of_prefix heq c.flatten_ne u.flatten_ne
  -- For closed/prefix the head of `c` is `a.head`; conclude a cycle.
  -- For infix/postfix this is the crux.  Generalize the fixity index so the
  -- match on `c` is well-typed.
  match (G.operator a).fixity, c, heq, hhd with
  | _, .closed w, _heq, hhd =>
      have hca : (Children.closed w).flatten.head? = some (G.operator a).head := by
        simpa only [Children.flatten] using w.flatten_head_op
      rw [hca, hh] at hhd
      have heads : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
      have hoa : o = a := Classical.byContradiction (fun hne => hG.heads_distinct hne heads.symm)
      subst hoa
      exact no_cycle hb hr
  | _, .prefix w t, _heq, hhd =>
      have hca : (Children.prefix w t).flatten.head? = some (G.operator a).head := by
        simp only [Children.flatten]
        rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
      rw [hca, hh] at hhd
      have heads : (G.operator a).head = (G.operator o).head := Option.some.inj hhd
      have hoa : o = a := Classical.byContradiction (fun hne => hG.heads_distinct hne heads.symm)
      subst hoa
      exact no_cycle hb hr
  | _, .postfix t w, heq, _hhd =>
      -- lead = t : Tree G a, mid = w.flatten ++ s₁
      have hmid : (w.flatten ++ s₁).head? = some (G.operator a).head := by
        rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
      refine crux_infixPostfix hG hb ReachTighter.refl t u (w.flatten ++ s₁) s₂ hmid ?_
      simpa only [Children.flatten, List.append_assoc] using heq
  | _, .infixL l w r, heq, _hhd =>
      -- lead = l : Tree G a, mid = w.flatten ++ r.flatten ++ s₁
      have hmid : (w.flatten ++ (r.flatten ++ s₁)).head? = some (G.operator a).head := by
        rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
      refine crux_infixPostfix hG hb ReachTighter.refl l u
        (w.flatten ++ (r.flatten ++ s₁)) s₂ hmid ?_
      simpa only [Children.flatten, List.append_assoc] using heq
  | _, .infixR l w r, heq, _hhd =>
      -- lead = inner Tree of l : TreeBelow G a
      obtain ⟨d, hd, lt⟩ := l
      have hmid : (w.flatten ++ (r.flatten ++ s₁)).head? = some (G.operator a).head := by
        rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
      refine crux_infixPostfix hG hb (ReachTighter.step hd ReachTighter.refl) lt u
        (w.flatten ++ (r.flatten ++ s₁)) s₂ hmid ?_
      simpa only [Children.flatten, TreeBelow.flatten, List.append_assoc] using heq
  | _, .infixN l w r, heq, _hhd =>
      obtain ⟨d, hd, lt⟩ := l
      have hmid : (w.flatten ++ (r.flatten ++ s₁)).head? = some (G.operator a).head := by
        rw [head?_append_left w.flatten_ne]; exact w.flatten_head_op
      refine crux_infixPostfix hG hb (ReachTighter.step hd ReachTighter.refl) lt u
        (w.flatten ++ (r.flatten ++ s₁)) s₂ hmid ?_
      simpa only [Children.flatten, TreeBelow.flatten, List.append_assoc] using heq

/-- `Woven G []` is uninhabited (every weave has at least one name-part). -/
theorem Woven.not_nil (w : Woven G []) : False := by cases w

mutual
  theorem udTree (hG : Unambiguous G) {a : G.Op} (t₁ t₂ : Tree G a) (s₁ s₂ : List Token)
      (h : t₁.flatten ++ s₁ = t₂.flatten ++ s₂) : t₁ = t₂ ∧ s₁ = s₂ :=
    match t₁ with
    | .op _ c₁ => by
        cases t₂ with
        | op _ c₂ =>
            have heqc : c₁.flatten ++ s₁ = c₂.flatten ++ s₂ := by
              simpa only [Tree.flatten] using h
            have hc := udChildren hG c₁ c₂ s₁ s₂ heqc
            exact ⟨by rw [hc.1], hc.2⟩
        | next tb₂ =>
            obtain ⟨b, hb, u⟩ := tb₂
            exact (udOpNext hG c₁ b hb u s₁ s₂ h).elim
    | .next tb₁ => by
        obtain ⟨b₁, hb₁, u₁⟩ := tb₁
        cases t₂ with
        | op _ c₂ =>
            exact (udOpNext hG c₂ b₁ hb₁ u₁ s₂ s₁ h.symm).elim
        | next tb₂ =>
            obtain ⟨b₂, hb₂, u₂⟩ := tb₂
            have heq : u₁.flatten ++ s₁ = u₂.flatten ++ s₂ := by
              simpa only [Tree.flatten, TreeBelow.flatten] using h
            have hhd : u₁.flatten.head? = u₂.flatten.head? :=
              head?_eq_of_prefix heq u₁.flatten_ne u₂.flatten_ne
            obtain ⟨o₁, hr₁, hh₁⟩ := u₁.headTok_reach
            obtain ⟨o₂, hr₂, hh₂⟩ := u₂.headTok_reach
            have hheads : (G.operator o₁).head = (G.operator o₂).head := by
              rw [hh₁, hh₂] at hhd; exact Option.some.inj hhd
            have ho : o₁ = o₂ :=
              Classical.byContradiction (fun hne => hG.heads_distinct hne hheads)
            subst ho
            by_cases hb : b₁ = b₂
            · subst hb
              have hrec := udTree hG u₁ u₂ s₁ s₂ heq
              exact ⟨by rw [hrec.1], hrec.2⟩
            · exact (hG.tighter_disjoint a b₁ b₂ hb₁ hb₂ hb o₁ hr₁ hr₂).elim
  termination_by structural t₁

  theorem udTreeBelow (hG : Unambiguous G) {a : G.Op}
      (tb₁ tb₂ : TreeBelow G a) (s₁ s₂ : List Token)
      (h : tb₁.flatten ++ s₁ = tb₂.flatten ++ s₂) : tb₁ = tb₂ ∧ s₁ = s₂ :=
    match tb₁ with
    | .mk b₁ hb₁ u₁ => by
        obtain ⟨b₂, hb₂, u₂⟩ := tb₂
        have heq : u₁.flatten ++ s₁ = u₂.flatten ++ s₂ := by
          simpa only [TreeBelow.flatten] using h
        have hhd : u₁.flatten.head? = u₂.flatten.head? :=
          head?_eq_of_prefix heq u₁.flatten_ne u₂.flatten_ne
        obtain ⟨o₁, hr₁, hh₁⟩ := u₁.headTok_reach
        obtain ⟨o₂, hr₂, hh₂⟩ := u₂.headTok_reach
        have hheads : (G.operator o₁).head = (G.operator o₂).head := by
          rw [hh₁, hh₂] at hhd; exact Option.some.inj hhd
        have ho : o₁ = o₂ :=
          Classical.byContradiction (fun hne => hG.heads_distinct hne hheads)
        subst ho
        by_cases hb : b₁ = b₂
        · subst hb
          have hrec := udTree hG u₁ u₂ s₁ s₂ heq
          exact ⟨by rw [hrec.1], hrec.2⟩
        · exact (hG.tighter_disjoint a b₁ b₂ hb₁ hb₂ hb o₁ hr₁ hr₂).elim
  termination_by structural tb₁

  theorem udWoven (hG : Unambiguous G) {parts : List Token}
      (w₁ w₂ : Woven G parts) (s₁ s₂ : List Token)
      (h : w₁.flatten ++ s₁ = w₂.flatten ++ s₂) : w₁ = w₂ ∧ s₁ = s₂ :=
    match w₁, w₂ with
    | .last tk, w₂ => by
        cases w₂ with
        | last tk' =>
            refine ⟨rfl, ?_⟩
            simpa only [Woven.flatten, List.cons_append, List.nil_append,
              List.cons.injEq, true_and] using h
        | cons tk' e w => exact (w.not_nil).elim
    | .cons tk e₁ w₁', w₂ => by
        cases w₂ with
        | last tk' => exact (w₁'.not_nil).elim
        | cons _ e₂ w₂' =>
            have heq : e₁.flatten ++ (w₁'.flatten ++ s₁)
                     = e₂.flatten ++ (w₂'.flatten ++ s₂) := by
              have h' : [tk] ++ (e₁.flatten ++ (w₁'.flatten ++ s₁))
                      = [tk] ++ (e₂.flatten ++ (w₂'.flatten ++ s₂)) := by
                simpa only [Woven.flatten, List.append_assoc] using h
              exact List.append_cancel_left h'
            have hrec := udExpr hG e₁ e₂ (w₁'.flatten ++ s₁) (w₂'.flatten ++ s₂) heq
            have hrec2 := udWoven hG w₁' w₂' s₁ s₂ hrec.2
            exact ⟨by rw [hrec.1, hrec2.1], hrec2.2⟩
  termination_by structural w₁

  theorem udExpr (hG : Unambiguous G) (e₁ e₂ : Expr G) (s₁ s₂ : List Token)
      (h : e₁.flatten ++ s₁ = e₂.flatten ++ s₂) : e₁ = e₂ ∧ s₁ = s₂ :=
    match e₁ with
    | .mk r₁ hr₁ t₁ => by
        obtain ⟨r₂, hr₂, t₂⟩ := e₂
        have heq : t₁.flatten ++ s₁ = t₂.flatten ++ s₂ := by
          simpa only [Expr.flatten] using h
        have hhd : t₁.flatten.head? = t₂.flatten.head? :=
          head?_eq_of_prefix heq t₁.flatten_ne t₂.flatten_ne
        obtain ⟨o₁, ho₁, hh₁⟩ := t₁.headTok_reach
        obtain ⟨o₂, ho₂, hh₂⟩ := t₂.headTok_reach
        have hheads : (G.operator o₁).head = (G.operator o₂).head := by
          rw [hh₁, hh₂] at hhd; exact Option.some.inj hhd
        have ho : o₁ = o₂ :=
          Classical.byContradiction (fun hne => hG.heads_distinct hne hheads)
        subst ho
        by_cases hr : r₁ = r₂
        · subst hr
          have hrec := udTree hG t₁ t₂ s₁ s₂ heq
          exact ⟨by rw [hrec.1], hrec.2⟩
        · exact (hG.loosest_disjoint r₁ r₂ hr₁ hr₂ hr o₁ ho₁ ho₂).elim
  termination_by structural e₁

  theorem udChildren (hG : Unambiguous G) {a : G.Op} {f : Fixity}
      (c₁ c₂ : Children G a f) (s₁ s₂ : List Token)
      (h : c₁.flatten ++ s₁ = c₂.flatten ++ s₂) : c₁ = c₂ ∧ s₁ = s₂ :=
    match c₁, c₂ with
    | .closed w₁, c₂ => by
        cases c₂ with
        | closed w₂ =>
            have heq : w₁.flatten ++ s₁ = w₂.flatten ++ s₂ := by
              simpa only [Children.flatten] using h
            have hrec := udWoven hG w₁ w₂ s₁ s₂ heq
            exact ⟨by rw [hrec.1], hrec.2⟩
    | .prefix w₁ t₁, c₂ => by
        cases c₂ with
        | «prefix» w₂ t₂ =>
            have heq : w₁.flatten ++ (t₁.flatten ++ s₁)
                     = w₂.flatten ++ (t₂.flatten ++ s₂) := by
              simpa only [Children.flatten, List.append_assoc] using h
            have hw := udWoven hG w₁ w₂ (t₁.flatten ++ s₁) (t₂.flatten ++ s₂) heq
            have ht := udTree hG t₁ t₂ s₁ s₂ hw.2
            exact ⟨by rw [hw.1, ht.1], ht.2⟩
    | .postfix t₁ w₁, c₂ => by
        cases c₂ with
        | «postfix» t₂ w₂ =>
            have heq : t₁.flatten ++ (w₁.flatten ++ s₁)
                     = t₂.flatten ++ (w₂.flatten ++ s₂) := by
              simpa only [Children.flatten, List.append_assoc] using h
            have ht := udTree hG t₁ t₂ (w₁.flatten ++ s₁) (w₂.flatten ++ s₂) heq
            have hw := udWoven hG w₁ w₂ s₁ s₂ ht.2
            exact ⟨by rw [ht.1, hw.1], hw.2⟩
    | .infixL l₁ w₁ r₁, c₂ => by
        cases c₂ with
        | infixL l₂ w₂ r₂ =>
            have heq : l₁.flatten ++ (w₁.flatten ++ (r₁.flatten ++ s₁))
                     = l₂.flatten ++ (w₂.flatten ++ (r₂.flatten ++ s₂)) := by
              simpa only [Children.flatten, List.append_assoc] using h
            have hl := udTree hG l₁ l₂ (w₁.flatten ++ (r₁.flatten ++ s₁))
              (w₂.flatten ++ (r₂.flatten ++ s₂)) heq
            have hw := udWoven hG w₁ w₂ (r₁.flatten ++ s₁) (r₂.flatten ++ s₂) hl.2
            have hr := udTreeBelow hG r₁ r₂ s₁ s₂ hw.2
            exact ⟨by rw [hl.1, hw.1, hr.1], hr.2⟩
    | .infixR l₁ w₁ r₁, c₂ => by
        cases c₂ with
        | infixR l₂ w₂ r₂ =>
            have heq : l₁.flatten ++ (w₁.flatten ++ (r₁.flatten ++ s₁))
                     = l₂.flatten ++ (w₂.flatten ++ (r₂.flatten ++ s₂)) := by
              simpa only [Children.flatten, List.append_assoc] using h
            have hl := udTreeBelow hG l₁ l₂ (w₁.flatten ++ (r₁.flatten ++ s₁))
              (w₂.flatten ++ (r₂.flatten ++ s₂)) heq
            have hw := udWoven hG w₁ w₂ (r₁.flatten ++ s₁) (r₂.flatten ++ s₂) hl.2
            have hr := udTree hG r₁ r₂ s₁ s₂ hw.2
            exact ⟨by rw [hl.1, hw.1, hr.1], hr.2⟩
    | .infixN l₁ w₁ r₁, c₂ => by
        cases c₂ with
        | infixN l₂ w₂ r₂ =>
            have heq : l₁.flatten ++ (w₁.flatten ++ (r₁.flatten ++ s₁))
                     = l₂.flatten ++ (w₂.flatten ++ (r₂.flatten ++ s₂)) := by
              simpa only [Children.flatten, List.append_assoc] using h
            have hl := udTreeBelow hG l₁ l₂ (w₁.flatten ++ (r₁.flatten ++ s₁))
              (w₂.flatten ++ (r₂.flatten ++ s₂)) heq
            have hw := udWoven hG w₁ w₂ (r₁.flatten ++ s₁) (r₂.flatten ++ s₂) hl.2
            have hr := udTreeBelow hG r₁ r₂ s₁ s₂ hw.2
            exact ⟨by rw [hl.1, hw.1, hr.1], hr.2⟩
  termination_by structural c₁

end

/-- **The hard direction** (was the open `sorry`). The syntactic criterion
`Unambiguous G` implies `flatten` is injective on `Expr G`.

Proof skeleton (all sorry-free except the isolated `crux_infixPostfix`):
`headTok_reach` (leading token of a tree is a reachable operator's head),
`no_cycle` (acyclicity of `tighter`), and a mutual prefix-form
unique-decomposition over the whole tree family (`udTree`/`udTreeBelow`/
`udWoven`/`udExpr`/`udChildren`), with the `op`-vs-`next` discrimination in
`udOpNext`.  The single remaining gap is `crux_infixPostfix` (the infix/postfix
leading-operand case). -/
theorem unambiguous_flatten_injective (hG : Unambiguous G) : FlattenInjective G := by
  intro e₁ e₂ he
  have heq : e₁.flatten ++ [] = e₂.flatten ++ [] := by simpa using he
  exact (udExpr hG e₁ e₂ [] [] heq).1

end LambdaLab.Parser.Playground
