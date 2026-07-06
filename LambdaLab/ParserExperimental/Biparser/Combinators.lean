import LambdaLab.ParserExperimental.Biparser.Basic

/-!
# Verified biparser combinators, *with* print policies

Combinators for the full `ParserExperimental.Biparser α Policy β` — both coherence laws
(`render_complete` + `parse_complete`) and the policy-indexed renderer. Each combinator
carries a **canonical policy type** (`tok` → `Unit`, `seq` → `P × Q`), which accumulates
into an ugly nested product as you build. `mapPolicy` reshapes it: a **surjective**
`f : Q → P` re-indexes a `P`-biparser by a nicer `Q`, keeping both laws
(`render_complete` needs `f` surjective; `parse_complete` needs nothing). Since it is
just `Biparser → Biparser`, it applies at any intermediate construction, not only the
end.
-/

namespace LambdaLab.ParserExperimental.RightSublist

/-- Re-index a right-sublist along a proof that its host list equals another. The
`list`/`pre` payload is unchanged (only the `eq` field is transported), so `.list` is
preserved definitionally — this is the plumbing `seq` needs to thread `parse` leftovers
whose types are indexed by the (only propositionally-known) remaining input. -/
def cast {α : Type} {l l' : List α} (h : l = l') (s : RightSublist l) : RightSublist l' :=
  ⟨s.list, s.pre, s.pre_ne, h ▸ s.eq⟩

@[simp] theorem cast_list {α : Type} {l l' : List α} (h : l = l') (s : RightSublist l) :
    (s.cast h).list = s.list := rfl

theorem cast_rfl {α : Type} {l : List α} (s : RightSublist l) : s.cast rfl = s := rfl

end LambdaLab.ParserExperimental.RightSublist

namespace LambdaLab.ParserExperimental


/-- Membership transports along a host-list equality (with the leftover `cast`), for
any parse-shaped function `f : (l : List α) → List (γ × RightSublist l)`. -/
theorem mem_cast_gen {α γ : Type} (f : (l : List α) → List (γ × RightSublist l))
    {l l' : List α} (h : l = l') {x : γ} {s : RightSublist l} (hm : (x, s) ∈ f l) :
    (x, s.cast h) ∈ f l' := by
  subst h; simpa [RightSublist.cast_rfl] using hm

/-- The `Biparser.parse` specialization of `mem_cast_gen`. -/
theorem mem_parse_cast {α Q γ : Type} (pc : Biparser α Q γ) {l l' : List α} (h : l = l')
    {x : γ} {s : RightSublist l} (hm : (x, s) ∈ pc.parse l) :
    (x, s.cast h) ∈ pc.parse l' :=
  mem_cast_gen pc.parse h hm

/-! ## Primitive: one predicate-satisfying token (policy `Unit`) -/

def tok {α : Type} (p : α → Bool) : Biparser α Unit { x : α // p x = true } where
  render x _ := [x.val]
  parse
    | []      => []
    | c :: cs => if h : p c = true then [(⟨c, h⟩, RightSublist.cons c cs)] else []
  render_complete := by
    intro input x s hmem
    refine ⟨(), ?_⟩
    cases input with
    | nil => simp at hmem
    | cons c cs =>
      by_cases h : p c = true
      · simp only [h, dite_true, List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨hx, hs⟩ := hmem
        subst hx; subst hs; rfl
      · simp [h] at hmem
  parse_complete := by
    intro x _ rest
    obtain ⟨c, hc⟩ := x
    refine ⟨RightSublist.cons c rest, rfl, ?_⟩
    show (⟨c, hc⟩, RightSublist.cons c rest) ∈
        (if h : p c = true then [((⟨c, h⟩ : { x : α // p x = true }), RightSublist.cons c rest)] else [])
    rw [dif_pos hc, List.mem_singleton]

/-! ## Combinator: sequence (policy `P × Q`) -/

def seq {α P Q β γ : Type} (pb : Biparser α P β) (pc : Biparser α Q γ) :
    Biparser α (P × Q) (β × γ) where
  render bc pq := pb.render bc.1 pq.1 ++ pc.render bc.2 pq.2
  parse input := (pb.parse input).flatMap fun r =>
    (pc.parse r.2.list).map fun r' => ((r.1, r'.1), r.2.trans r'.2)
  render_complete := by
    intro input bc s hmem
    simp only [List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨⟨b, s'⟩, hb, ⟨c, s''⟩, hc, heq⟩ := hmem
    rw [Prod.mk.injEq] at heq
    obtain ⟨hbc, hs⟩ := heq
    obtain ⟨pp, hpp⟩ := pb.render_complete input b s' hb
    obtain ⟨qq, hqq⟩ := pc.render_complete s'.list c s'' hc
    refine ⟨(pp, qq), ?_⟩
    subst hbc; subst hs
    show pb.render b pp ++ pc.render c qq = (s'.trans s'').pre
    rw [hpp, hqq]; rfl
  parse_complete := by
    intro bc pq rest
    obtain ⟨b, c⟩ := bc; obtain ⟨p, q⟩ := pq
    -- `render` concatenates left-assoc `(A ++ B) ++ rest`; `parse_complete` peels `A`
    -- leaving `A ++ (B ++ rest)`. Reassociate the whole goal so the indices line up.
    rw [List.append_assoc]
    obtain ⟨s1, hs1, hb⟩ := pb.parse_complete b p (pc.render c q ++ rest)
    obtain ⟨s2, hs2, hc⟩ := pc.parse_complete c q rest
    refine ⟨s1.trans (s2.cast hs1.symm), ?_, ?_⟩
    · show (s2.cast hs1.symm).list = rest
      simp [hs2]
    · simp only [List.mem_flatMap, List.mem_map]
      exact ⟨(b, s1), hb, (c, s2.cast hs1.symm), mem_parse_cast pc hs1.symm hc, rfl⟩

/-! ## Combinator: reshape the policy along a surjection -/

def mapPolicy {α P Q β : Type} (f : Q → P) (hf : ∀ p, ∃ q, f q = p)
    (pb : Biparser α P β) : Biparser α Q β where
  render b q := pb.render b (f q)
  parse := pb.parse
  render_complete := by
    intro input e s hmem
    obtain ⟨p, hp⟩ := pb.render_complete input e s hmem
    obtain ⟨q, hq⟩ := hf p
    exact ⟨q, by show pb.render e (f q) = s.pre; rw [hq]; exact hp⟩
  parse_complete := by
    intro e q rest
    exact pb.parse_complete e (f q) rest

/-! ## Combinator: map the value along a bijection -/

/-- Transport a biparser's value type along a bijection `to`/`fro` (`fro ∘ to = id`,
`to ∘ fro = id`). Used to turn raw parse shapes (subtype pairs, digit lists) into real
AST values without touching the policy. -/
def map {α P β γ : Type} (pb : Biparser α P β) (to : β → γ) (fro : γ → β)
    (hlr : ∀ b, fro (to b) = b) (hrl : ∀ c, to (fro c) = c) : Biparser α P γ where
  render c p := pb.render (fro c) p
  parse input := (pb.parse input).map fun r => (to r.1, r.2)
  render_complete := by
    intro input c s hmem
    simp only [List.mem_map] at hmem
    obtain ⟨⟨b, s'⟩, hb, heq⟩ := hmem
    rw [Prod.mk.injEq] at heq
    obtain ⟨hc, hs⟩ := heq
    obtain ⟨p, hp⟩ := pb.render_complete input b s' hb
    refine ⟨p, ?_⟩
    subst hc; subst hs
    show pb.render (fro (to b)) p = s'.pre
    rw [hlr]; exact hp
  parse_complete := by
    intro c p rest
    obtain ⟨s, hs, hb⟩ := pb.parse_complete (fro c) p rest
    refine ⟨s, hs, ?_⟩
    simp only [List.mem_map]
    exact ⟨(fro c, s), hb, by rw [hrl]⟩

/-! ## Combinator: alternation (choice) -/

/-- Ordered choice: parse `pb` or `pc`, tagging the value with `Sum`. Both laws hold
**unconditionally** in the all-parses model — `parse` returns every parse of both
branches, so `render_complete`/`parse_complete` just read off the relevant branch (no
distinguishability side-condition needed; that only matters for *determinism*). The
policy carries both sub-policies; `Inhabited` supplies the unused one. -/
def alt {α P Q β γ : Type} [Inhabited P] [Inhabited Q]
    (pb : Biparser α P β) (pc : Biparser α Q γ) : Biparser α (P × Q) (β ⊕ γ) where
  render v pq := match v with
    | .inl b => pb.render b pq.1
    | .inr c => pc.render c pq.2
  parse input := (pb.parse input).map (fun r => (Sum.inl r.1, r.2)) ++
                 (pc.parse input).map (fun r => (Sum.inr r.1, r.2))
  render_complete := by
    intro input v s hmem
    simp only [List.mem_append, List.mem_map] at hmem
    rcases hmem with ⟨⟨b, s'⟩, hb, heq⟩ | ⟨⟨c, s'⟩, hc, heq⟩
    · rw [Prod.mk.injEq] at heq
      obtain ⟨hv, hs⟩ := heq
      obtain ⟨p, hp⟩ := pb.render_complete input b s' hb
      exact ⟨(p, default), by subst hv; subst hs; exact hp⟩
    · rw [Prod.mk.injEq] at heq
      obtain ⟨hv, hs⟩ := heq
      obtain ⟨q, hq⟩ := pc.render_complete input c s' hc
      exact ⟨(default, q), by subst hv; subst hs; exact hq⟩
  parse_complete := by
    intro v pq rest
    match v with
    | .inl b =>
      obtain ⟨s, hs, hb⟩ := pb.parse_complete b pq.1 rest
      refine ⟨s, hs, ?_⟩
      simp only [List.mem_append, List.mem_map]
      exact Or.inl ⟨(b, s), hb, rfl⟩
    | .inr c =>
      obtain ⟨s, hs, hc⟩ := pc.parse_complete c pq.2 rest
      refine ⟨s, hs, ?_⟩
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨(c, s), hc, rfl⟩

/-! ## Combinator: `some` — one-or-more repetition

Recursive on the strictly-shrinking leftover (`RightSublist.length_lt`). The value is a
**nonempty** list `β × List β` (the model forbids a zero-consumption parse, so `some`,
not `many`). Policy is a single `P` applied **uniformly** — valid because we require
`[Subsingleton P]`, which lets `render_complete` unify the per-element policies. -/

def someParse {α P β : Type} (p : Biparser α P β) :
    (input : List α) → List ((β × List β) × RightSublist input)
  | input =>
    (p.parse input).flatMap fun r =>
      ((r.1, ([] : List β)), r.2) ::
        (someParse p r.2.list).map fun r' => ((r.1, r'.1.1 :: r'.1.2), r.2.trans r'.2)
  termination_by input => input.length
  decreasing_by exact r.2.length_lt

def someRender {α P β : Type} (p : Biparser α P β) (v : β × List β) (pol : P) : List α :=
  (v.1 :: v.2).flatMap fun x => p.render x pol

/-- `render_complete` for `some`, by structural induction on a length fuel `n`
(bounding the shrinking leftover). `Subsingleton P` unifies the head token's policy with
the tail's, so one uniform `pol` renders the whole nonempty list back to the consumed
prefix. -/
theorem some_render_complete_aux {α P β : Type} [Subsingleton P] (p : Biparser α P β) :
    ∀ (n : Nat) (input : List α), input.length ≤ n → ∀ (v : β × List β) (s : RightSublist input),
      (v, s) ∈ someParse p input → ∃ pol, someRender p v pol = s.pre := by
  intro n
  induction n with
  | zero =>
    intro input hlen v s _
    exfalso; have := s.length_lt; omega
  | succ n ih =>
    intro input hlen v s hmem
    rw [someParse] at hmem
    simp only [List.mem_flatMap, List.mem_cons, List.mem_map] at hmem
    obtain ⟨⟨b, s'⟩, hb, hcase⟩ := hmem
    rcases hcase with heq | ⟨⟨⟨b'', bs''⟩, s''⟩, hmem'', heq⟩
    · rw [Prod.mk.injEq] at heq
      obtain ⟨hv, hs⟩ := heq
      subst hv; subst hs
      obtain ⟨pol_b, hpb⟩ := p.render_complete input b s hb
      exact ⟨pol_b, by simp [someRender, hpb]⟩
    · rw [Prod.mk.injEq] at heq
      obtain ⟨hv, hs⟩ := heq
      obtain ⟨pol_b, hpb⟩ := p.render_complete input b s' hb
      have hlen' : s'.list.length ≤ n := by have := s'.length_lt; omega
      obtain ⟨pol', hp'⟩ := ih s'.list hlen' (b'', bs'') s'' hmem''
      refine ⟨pol_b, ?_⟩
      subst hv; subst hs
      have hren : someRender p (b, b'' :: bs'') pol_b
          = p.render b pol_b ++ someRender p (b'', bs'') pol_b := by simp [someRender]
      rw [hren, hpb, Subsingleton.elim pol_b pol', hp']
      rfl

theorem some_render_complete {α P β : Type} [Subsingleton P] (p : Biparser α P β)
    (input : List α) (v : β × List β) (s : RightSublist input)
    (hmem : (v, s) ∈ someParse p input) : ∃ pol, someRender p v pol = s.pre :=
  some_render_complete_aux p input.length input (Nat.le_refl _) v s hmem

def «some» {α P β : Type} [Subsingleton P] (p : Biparser α P β) :
    Biparser α P (β × List β) where
  render := someRender p
  parse := someParse p
  render_complete := fun input v s hmem => some_render_complete p input v s hmem
  parse_complete := by
    intro v pol rest
    obtain ⟨b, bs⟩ := v
    induction bs generalizing b rest with
    | nil =>
      have h0 : someRender p (b, []) pol = p.render b pol := by simp [someRender]
      rw [h0]
      obtain ⟨s1, hs1, hb⟩ := p.parse_complete b pol rest
      refine ⟨s1, hs1, ?_⟩
      rw [someParse]
      simp only [List.mem_flatMap]
      exact ⟨(b, s1), hb, List.mem_cons_self⟩
    | cons b' bs' ih =>
      have hren : someRender p (b, b' :: bs') pol
          = p.render b pol ++ someRender p (b', bs') pol := by simp [someRender]
      rw [hren, List.append_assoc]
      obtain ⟨s2, hs2, hmem2⟩ := ih (b := b') (rest := rest)
      obtain ⟨s1, hs1, hb⟩ := p.parse_complete b pol (someRender p (b', bs') pol ++ rest)
      refine ⟨s1.trans (s2.cast hs1.symm), ?_, ?_⟩
      · show (s2.cast hs1.symm).list = rest
        simp [hs2]
      · rw [someParse]
        simp only [List.mem_flatMap]
        refine ⟨(b, s1), hb, ?_⟩
        simp only [List.mem_cons, List.mem_map]
        exact Or.inr ⟨((b', bs'), s2.cast hs1.symm), mem_cast_gen (someParse p) hs1.symm hmem2, rfl⟩

/-! ## Example: `a b c` — canonical policy `Unit × (Unit × Unit)`, reshaped to `Unit`. -/

def three := seq (tok (· == 'a')) (seq (tok (· == 'b')) (tok (· == 'c')))

/-- Reshape the nested-product policy down to a single `Unit` (a bijection here, since
all the leaf policies are `Unit`; the surjection is discharged by `Subsingleton`). -/
def threeNice := mapPolicy (fun _ : Unit => ((), ((), ()))) (fun _ => ⟨(), Subsingleton.elim _ _⟩) three

#eval three.render (⟨'a', by decide⟩, ⟨'b', by decide⟩, ⟨'c', by decide⟩) ((), (), ())  -- ['a','b','c']
#eval (three.parse "abc".toList).map (fun r => (r.1, r.2.list))                          -- [((a,b,c), [])]
#eval (threeNice.parse "abcZ".toList).map (fun r => (r.1, r.2.list))                     -- [((a,b,c), ['Z'])]
#eval threeNice.render (⟨'a', by decide⟩, ⟨'b', by decide⟩, ⟨'c', by decide⟩) ()         -- ['a','b','c']

end LambdaLab.ParserExperimental
