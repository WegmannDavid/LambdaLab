import LambdaLab.Parser.Playground3.Parse

/-!
# Correctness of the `Part`/`Parts` parser

Three properties on top of `Parse.lean`'s termination:

* **Soundness** (`parseExpr_sound`, `parse_sound`) — every parse consumes
  exactly the tokens it claims: `e.flatten ++ rest.list = tkns`. Proved by the
  parser's own functional induction principle (`parseExpr.mutual_induct`).
* **Completeness** (`parseExpr_complete`, `parse_complete`) — every expression
  is found: `e ∈ parse e.flatten`. Proved by mutual induction on `Expr`/`Parts`
  with an inner descent along the `TighterEq` path (measured by `Grammar.rank`).
* **Uniqueness** (`parse_unique`) — reduced to `Grammar.Unambiguous`, the
  grammar-level property that flattening is injective on loosest expressions.
  Soundness pins every full parse's flattening to the input, so unambiguity
  collapses the result list to (copies of) a single tree. Discharging
  `Unambiguous` for a concrete grammar class is a separate (hard) problem.
-/

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

variable {G : Grammar}

/-! ## Flattening lemmas -/

@[simp] theorem Expr.flatten_op {l : Level G} (o : G.Op) (hc : Level.condition l o)
    (parts : Parts G (Part.parts o)) : (Expr.op o hc parts).flatten = parts.flatten := rfl

@[simp] theorem Parts.flatten_nil : (Parts.nil (G := G)).flatten = [] := rfl

@[simp] theorem Parts.flatten_hole {l : Level G} {ps : List (Part G)}
    (e : Expr G l) (p : Parts G ps) : (Parts.hole e p).flatten = e.flatten ++ p.flatten := rfl

@[simp] theorem Parts.flatten_namePart {ps : List (Part G)} (tk : Token) (p : Parts G ps) :
    (Parts.namePart tk p).flatten = tk :: p.flatten := rfl

/-- Reindexing only swaps the level-condition proof; the flattening is untouched. -/
@[simp] theorem Expr.flatten_reindex {l l' : Level G}
    (h : ∀ o, Level.condition l o → Level.condition l' o) (e : Expr G l) :
    (e.reindex h).flatten = e.flatten := by
  cases e; rfl

/-! ## `RightSublist` lemmas -/

@[simp] theorem RightSublist.list_cons {α : Type _} (a : α) (l : List α) :
    (RightSublist.cons a l).list = l := rfl

@[simp] theorem RightSublist.list_trans {α : Type _} {l : List α}
    (s : RightSublist l) (r : RightSublist s.list) : (s.trans r).list = r.list := rfl

/-! ## Soundness -/

/-- Joint soundness of the three mutual parser functions: every returned pair
`(tree, leftover)` satisfies `tree.flatten ++ leftover.list = tkns`. One
application of the parser's functional induction principle; each case is
list-membership bookkeeping. -/
theorem parse_sound_all :
    (∀ (l : Level G) (tkns : List Token),
        ∀ x ∈ parseExpr l tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (ps : List (Part G)) (tkns : List Token),
        ∀ x ∈ parseParts ps tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ ∀ (l : Level G) (cs : List G.Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq G.tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, G.rank c < Level.base l) (tkns : List Token),
      ∀ x ∈ parseExprList l cs h hrank tkns, x.1.flatten ++ x.2.list = tkns := by
  apply parseExpr.mutual_induct
    (motive1 := fun l tkns =>
      ∀ x ∈ parseExpr l tkns, x.1.flatten ++ x.2.list = tkns)
    (motive2 := fun ps tkns =>
      ∀ x ∈ parseParts ps tkns, x.1.flatten ++ x.2.list = tkns)
    (motive3 := fun l cs h hrank tkns =>
      ∀ x ∈ parseExprList l cs h hrank tkns, x.1.flatten ++ x.2.list = tkns)
  case _ => -- parseExpr .loosest
    intro tkns ih
    simpa [parseExpr] using ih
  case _ => -- parseExpr (.tighter a)
    intro a tkns ih
    simpa [parseExpr] using ih
  case _ => -- parseExpr (.tighterEq a)
    intro a tkns ihParts ihTighter x hx
    rw [parseExpr] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa using ihParts y hy
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa using ihTighter y hy
  case _ => -- parseParts []
    intro tkns x hx
    rw [parseParts] at hx
    simp at hx
  case _ => -- parseParts [namePart tk] (tk :: rest)
    intro t rest x hx
    rw [parseParts] at hx
    simp at hx
    simp [hx]
  case _ => -- parseParts [namePart tk] (t :: rest), t ≠ tk
    intro tk t rest hne x hx
    rw [parseParts] at hx
    simp [hne] at hx
  case _ => -- parseParts [namePart tk] []
    intro tk x hx
    rw [parseParts] at hx
    simp at hx
  case _ => -- parseParts [hole l]
    intro l tkns ih x hx
    rw [parseParts] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simpa using ih y hy
  case _ => -- parseParts (namePart tk :: y :: rest') (tk :: ts)
    intro y rest' t ts ih x hx
    rw [parseParts, if_pos rfl] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    simpa using congrArg (t :: ·) (ih z hz)
  case _ => -- parseParts (namePart tk :: y :: rest') (t :: ts), t ≠ tk
    intro tk y rest' t ts hne x hx
    rw [parseParts] at hx
    simp [hne] at hx
  case _ => -- parseParts (namePart tk :: y :: rest') []
    intro tk y rest' x hx
    rw [parseParts] at hx
    simp at hx
  case _ => -- parseParts (hole l :: y :: rest')
    intro l y rest' tkns ihInner ihExpr x hx
    rw [parseParts] at hx
    obtain ⟨w, hw, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    have h1 := ihExpr w hw
    have h2 := ihInner w z hz
    simp only [Parts.flatten_hole, RightSublist.list_trans, List.append_assoc, h2, h1]
  case _ => -- parseExprList l []
    intro l tkns _ _ _ _ x hx
    rw [parseExprList] at hx
    simp at hx
  case _ => -- parseExprList l (c :: rest)
    intro l tkns c rest h hrank _ _ ihExpr ihRest x hx
    rw [parseExprList] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa using ihExpr y hy
    · exact ihRest x hx

/-- Soundness of `parseExpr`: a parse at level `l` flattens back to exactly the
consumed prefix. -/
theorem parseExpr_sound {l : Level G} {tkns : List Token}
    {x : Expr G l × RightSublist tkns} (hx : x ∈ parseExpr l tkns) :
    x.1.flatten ++ x.2.list = tkns :=
  parse_sound_all.1 l tkns x hx

/-- Soundness of `parseParts`. -/
theorem parseParts_sound {ps : List (Part G)} {tkns : List Token}
    {x : Parts G ps × RightSublist tkns} (hx : x ∈ parseParts ps tkns) :
    x.1.flatten ++ x.2.list = tkns :=
  parse_sound_all.2.1 ps tkns x hx

/-- Soundness of `parse`: a full parse flattens back to the whole input. -/
theorem parse_sound {tkns : List Token} {e : Expr G .loosest} (h : e ∈ parse tkns) :
    e.flatten = tkns := by
  unfold parse at h
  obtain ⟨x, hx, hfm⟩ := List.mem_filterMap.mp h
  split at hfm
  next hnil =>
    cases hfm
    simpa [hnil] using parseExpr_sound hx
  next => cases hfm

/-! ## Completeness -/

/-- Reindexing is independent of the supplied weakening proof. -/
theorem Expr.reindex_irrel {l l' : Level G}
    (h h' : ∀ o, Level.condition l o → Level.condition l' o) (e : Expr G l) :
    e.reindex h = e.reindex h' := by
  cases e; rfl

/-- A strictly-tighter path decomposes into a first `tighter` step and a
tighter-or-equal remainder. -/
theorem Tighter.destruct {Op : Type} {t : Op → List Op} {a o : Op} (h : Tighter t a o) :
    ∃ b ∈ t a, TighterEq t b o := by
  cases h with
  | base hmem => exact ⟨o, hmem, TighterEq.refl⟩
  | step hmem hT => exact ⟨_, hmem, hT.toTighterEq⟩

theorem Part.inner_ne_nil (tkns : NonEmptyList Token) : Part.inner (G := G) tkns ≠ [] := by
  cases tkns <;> simp [Part.inner]

theorem Part.parts_ne_nil (o : G.Op) : Part.parts (G := G) o ≠ [] := by
  unfold Part.parts
  cases hop : G.operator o with
  | closed tkns => exact Part.inner_ne_nil tkns
  | infx tkns => simp

/-- Completeness of the candidate worklist: a parse found at a candidate's own
`tighterEq` level survives, reindexed, into `parseExprList`'s concatenation. -/
theorem parseExprList_complete {l : Level G} (cs : List G.Op)
    (h : ∀ c ∈ cs, ∀ o, TighterEq G.tighter c o → Level.condition l o)
    (hrank : ∀ c ∈ cs, G.rank c < Level.base l)
    {c : G.Op} (hc : c ∈ cs)
    (hcond : ∀ o, Level.condition (Level.tighterEq c) o → Level.condition l o)
    {tkns : List Token} {e : Expr G (.tighterEq c)} {r : RightSublist tkns}
    (hmem : (e, r) ∈ parseExpr (.tighterEq c) tkns) :
    (e.reindex hcond, r) ∈ parseExprList l cs h hrank tkns := by
  induction cs with
  | nil => cases hc
  | cons c' rest ih =>
      rw [parseExprList]
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact List.mem_append_left _ (List.mem_map.mpr
          ⟨(e, r), hmem, congrArg (fun t => (t, r)) (Expr.reindex_irrel _ hcond e)⟩)
      · exact List.mem_append_right _ (ih _ _ hc')

mutual

/-- Completeness of `parseParts`: a body inhabitant `p : Parts G ps` is found in
`parseParts ps` on its own flattening (any right-extension `rest`), leaving
exactly `rest`. (`ps = []` is excluded: `parseParts [] = []` by design, so the
parser never produces the empty-consuming `Parts.nil` on its own.) -/
theorem parseParts_complete {ps : List (Part G)} (p : Parts G ps) (hps : ps ≠ [])
    (tkns rest : List Token) (heq : tkns = p.flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧ (p, r) ∈ parseParts ps tkns := by
  match ps, p, heq with
  | [], _, _ => exact absurd rfl hps
  | [.namePart tk], .namePart _ .nil, heq =>
      simp only [Parts.flatten_namePart, Parts.flatten_nil, List.cons_append,
        List.nil_append] at heq
      subst heq
      refine ⟨.cons tk rest, rfl, ?_⟩
      rw [parseParts, if_pos rfl]
      exact List.mem_singleton.mpr rfl
  | [.hole l], .hole e .nil, heq =>
      simp only [Parts.flatten_hole, Parts.flatten_nil, List.append_nil] at heq
      obtain ⟨r, hr, hm⟩ := parseExpr_complete e tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseParts]
      exact List.mem_map.mpr ⟨(e, r), hm, rfl⟩
  | .namePart tk :: y :: rest', .namePart _ p', heq =>
      simp only [Parts.flatten_namePart, List.cons_append] at heq
      subst heq
      obtain ⟨r₂, hr₂, hm₂⟩ :=
        parseParts_complete p' (List.cons_ne_nil y rest') (p'.flatten ++ rest) rest rfl
      refine ⟨(RightSublist.cons tk (p'.flatten ++ rest)).trans r₂, by simp [hr₂], ?_⟩
      rw [parseParts, if_pos rfl]
      exact List.mem_map.mpr ⟨(p', r₂), hm₂, rfl⟩
  | .hole l :: y :: rest', .hole e p', heq =>
      simp only [Parts.flatten_hole, List.append_assoc] at heq
      obtain ⟨r₁, hr₁, hm₁⟩ :=
        parseExpr_complete e tkns (p'.flatten ++ rest) heq
      obtain ⟨r₂, hr₂, hm₂⟩ :=
        parseParts_complete p' (List.cons_ne_nil y rest') r₁.list rest hr₁
      refine ⟨r₁.trans r₂, by simp [hr₂], ?_⟩
      rw [parseParts]
      exact List.mem_flatMap.mpr ⟨(e, r₁), hm₁, List.mem_map.mpr ⟨(p', r₂), hm₂, rfl⟩⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals simp_wf
  all_goals exact Prod.Lex.left _ _ (by first | (simp; omega) | omega)

/-- Completeness at a `tighterEq` level, by descent along the `TighterEq` path:
either the path is trivial and the operator's own body parse applies, or it
factors through an immediately-tighter candidate, whose rank is smaller. -/
theorem parseExpr_tighterEq_complete {a o : G.Op} (hpath : TighterEq G.tighter a o)
    (parts : Parts G (Part.parts o)) (tkns rest : List Token)
    (heq : tkns = parts.flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op o hpath parts : Expr G (.tighterEq a)), r) ∈ parseExpr (.tighterEq a) tkns := by
  rcases hpath.toTighterOrEq with heqa | hT
  · obtain ⟨r, hr, hm⟩ := parseParts_complete parts (Part.parts_ne_nil o) tkns rest heq
    subst heqa
    refine ⟨r, hr, ?_⟩
    rw [parseExpr]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨(parts, r), hm, rfl⟩)
  · obtain ⟨b, hb, hpath'⟩ := hT.destruct
    obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath' parts tkns rest heq
    refine ⟨r, hr, ?_⟩
    have hmem2 : ((Expr.op o hpath' parts : Expr G (.tighterEq b)).reindex
        (l := .tighterEq b) (l' := .tighter a)
        (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr (.tighter a) tkns := by
      rw [parseExpr]
      exact parseExprList_complete (l := .tighter a) (G.tighter a)
        (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => G.rank_lt hc)
        hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm
    rw [parseExpr]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem2, rfl⟩)
termination_by (sizeOf parts, G.rank a + 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.right _ (by have := G.rank_lt hb; omega)
    | exact Prod.Lex.right _ (by omega)

/-- Completeness of `parseExpr`: every `e : Expr G l` is found on its own
flattening (any right-extension `rest`), leaving exactly `rest`. -/
theorem parseExpr_complete {l : Level G} (e : Expr G l) (tkns rest : List Token)
    (heq : tkns = e.flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧ (e, r) ∈ parseExpr l tkns := by
  match l, e, heq with
  | .tighterEq a, .op o hc parts, heq =>
      exact parseExpr_tighterEq_complete hc parts tkns rest heq
  | .tighter a, .op o hc parts, heq =>
      obtain ⟨b, hb, hpath⟩ := Tighter.destruct hc
      obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseExpr]
      exact parseExprList_complete (l := .tighter a) (G.tighter a)
        (fun _ hcc _o hco => Tighter.ofMemTighterEq hcc hco) (fun _ hcc => G.rank_lt hcc)
        hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm
  | .loosest, .op o hc parts, heq =>
      obtain ⟨a, ha, hpath⟩ := hc
      obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseExpr]
      exact parseExprList_complete (l := .loosest) G.loosest
        (fun c hcc _o hco => ⟨c, hcc, hco⟩) (fun _ hcc => G.rank_lt_topRank hcc)
        ha (fun _o hh => ⟨a, ha, hh⟩) hm
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals exact Prod.Lex.left _ _ (by first | (simp; omega) | omega)

end

/-- Completeness of `parse`: every loosest expression is a full parse of its
own flattening. -/
theorem parse_complete (e : Expr G .loosest) : e ∈ parse e.flatten := by
  obtain ⟨r, hr, hm⟩ := parseExpr_complete e e.flatten [] (by simp)
  unfold parse
  exact List.mem_filterMap.mpr ⟨(e, r), hm, by simp [hr]⟩

/-- The full characterization of `parse` as a set: its members are exactly the
loosest expressions flattening to the input. (Soundness + completeness.) -/
theorem mem_parse_iff {tkns : List Token} {e : Expr G .loosest} :
    e ∈ parse tkns ↔ e.flatten = tkns :=
  ⟨parse_sound, fun h => h ▸ parse_complete e⟩

/-! ## Uniqueness -/

/-- A grammar is **unambiguous** when flattening is injective on loosest
expressions: no token string is the flattening of two distinct trees. This is a
property of the *grammar*, not the parser — by `mem_parse_iff` the parser
returns exactly the trees flattening to the input, so unambiguity is precisely
what collapses the result list to copies of a single tree. Discharging it for a
concrete grammar (class) is a separate problem. -/
def Grammar.Unambiguous (G : Grammar) : Prop :=
  ∀ (e₁ e₂ : Expr G .loosest), e₁.flatten = e₂.flatten → e₁ = e₂

/-- Uniqueness of full parses, conditional on grammar unambiguity: any two
members of `parse tkns` are equal (the list may still contain duplicates when
the precedence DAG reaches an operator along several paths). -/
theorem parse_unique (hG : G.Unambiguous) {tkns : List Token}
    {e₁ e₂ : Expr G .loosest} (h₁ : e₁ ∈ parse tkns) (h₂ : e₂ ∈ parse tkns) :
    e₁ = e₂ :=
  hG e₁ e₂ ((parse_sound h₁).trans (parse_sound h₂).symm)

end LambdaLab.Parser.Playground3
