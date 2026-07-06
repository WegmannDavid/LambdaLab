import LambdaLab.ParserExperimental1.Biparser.Basic

/-!
# Biparser combinators for the weaker (renderer-soundness-only) target

Combinators for `ParserExperimental1.Biparser α Policy β`, which keeps **only**
`parse_complete` (every policy round-trips) and drops `render_complete`. Because
`render_complete` was the sole source of every side-condition, this variant is markedly
simpler than the two-law version: `mapPolicy` needs no surjectivity, `map` needs no
left-inverse, `alt` needs no `Inhabited`, and `«some»` needs no `[Subsingleton]`. Each
combinator carries a **canonical policy type** (`tok` → `Unit`, `seq` → `P × Q`), which
accumulates into a nested product; `mapPolicy` reshapes it along *any* `f : Q → P`.
-/

namespace LambdaLab.ParserExperimental1.RightSublist

/-- Re-index a right-sublist along a proof that its host list equals another. The
`list`/`pre` payload is unchanged (only the `eq` field is transported), so `.list` is
preserved definitionally — this is the plumbing `seq`/`some` need to thread `parse`
leftovers whose types are indexed by the (only propositionally-known) remaining input. -/
def cast {α : Type} {l l' : List α} (h : l = l') (s : RightSublist l) : RightSublist l' :=
  ⟨s.list, s.pre, s.pre_ne, h ▸ s.eq⟩

@[simp] theorem cast_list {α : Type} {l l' : List α} (h : l = l') (s : RightSublist l) :
    (s.cast h).list = s.list := rfl

theorem cast_rfl {α : Type} {l : List α} (s : RightSublist l) : s.cast rfl = s := rfl

end LambdaLab.ParserExperimental1.RightSublist

namespace LambdaLab.ParserExperimental1

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

/-! ## Combinator: reshape the policy along *any* map

With `render_complete` gone, no surjectivity is needed — a non-surjective `f` just means
fewer reachable renderings, which the weaker target permits. -/

def mapPolicy {α P Q β : Type} (f : Q → P) (pb : Biparser α P β) : Biparser α Q β where
  render b q := pb.render b (f q)
  parse := pb.parse
  parse_complete := by
    intro e q rest
    exact pb.parse_complete e (f q) rest

/-! ## Combinator: map the value along a section

Only the right-inverse `to ∘ fro = id` is needed now (the left-inverse was for
`render_complete`). So `map` transports along a *section*, not a full bijection. -/

def map {α P β γ : Type} (pb : Biparser α P β) (to : β → γ) (fro : γ → β)
    (hrl : ∀ c, to (fro c) = c) : Biparser α P γ where
  render c p := pb.render (fro c) p
  parse input := (pb.parse input).map fun r => (to r.1, r.2)
  parse_complete := by
    intro c p rest
    obtain ⟨s, hs, hb⟩ := pb.parse_complete (fro c) p rest
    refine ⟨s, hs, ?_⟩
    simp only [List.mem_map]
    exact ⟨(fro c, s), hb, by rw [hrl]⟩

/-! ## Combinator: alternation (choice)

No `Inhabited` needed now — that was only to supply the *unused* policy component in
`render_complete`. The policy carries both sub-policies; `render` reads the one matching
the value, so it is total with no default. -/

def alt {α P Q β γ : Type} (pb : Biparser α P β) (pc : Biparser α Q γ) :
    Biparser α (P × Q) (β ⊕ γ) where
  render v pq := match v with
    | .inl b => pb.render b pq.1
    | .inr c => pc.render c pq.2
  parse input := (pb.parse input).map (fun r => (Sum.inl r.1, r.2)) ++
                 (pc.parse input).map (fun r => (Sum.inr r.1, r.2))
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
not `many`). Policy is a single `P` applied uniformly. No `[Subsingleton P]` needed for
the weaker target — that was only to unify per-element policies in `render_complete`. -/

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

def «some» {α P β : Type} (p : Biparser α P β) : Biparser α P (β × List β) where
  render := someRender p
  parse := someParse p
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

/-- Reshape the nested-product policy down to a single `Unit` along any map (no
surjectivity obligation in the weaker target). -/
def threeNice := mapPolicy (fun _ : Unit => ((), ((), ()))) three

#eval three.render (⟨'a', by decide⟩, ⟨'b', by decide⟩, ⟨'c', by decide⟩) ((), (), ())  -- ['a','b','c']
#eval (three.parse "abc".toList).map (fun r => (r.1, r.2.list))                          -- [((a,b,c), [])]
#eval (threeNice.parse "abcZ".toList).map (fun r => (r.1, r.2.list))                     -- [((a,b,c), ['Z'])]
#eval threeNice.render (⟨'a', by decide⟩, ⟨'b', by decide⟩, ⟨'c', by decide⟩) ()         -- ['a','b','c']

end LambdaLab.ParserExperimental1
