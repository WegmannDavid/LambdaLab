import LambdaLab.Parser.Mixfix.Parse

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

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

variable {G : Grammar}

/-! ## Flattening lemmas -/

@[simp] theorem Expr.flatten_op {l : Level G} (o : G.Op) (hc : Level.condition l o)
    (parts : Parts G (Part.parts o)) : (Expr.op o hc parts).flatten = parts.flatten := rfl

@[simp] theorem Expr.flatten_var {l : Level G} (t : Token) (hv : G.isVar t = true) :
    (Expr.var (G := G) (l := l) t hv).flatten = [t] := rfl

@[simp] theorem Parts.flatten_nil : (Parts.nil (G := G)).flatten = [] := rfl

@[simp] theorem Parts.flatten_hole {l : Level G} {ps : List (Part G)}
    (e : Expr G l) (p : Parts G ps) : (Parts.hole e p).flatten = e.flatten ++ p.flatten := rfl

@[simp] theorem Parts.flatten_namePart {ps : List (Part G)} (tk : Token) (p : Parts G ps) :
    (Parts.namePart tk p).flatten = tk :: p.flatten := rfl

/-- Reindexing only swaps the level-condition proof; the flattening is untouched. -/
@[simp] theorem Expr.flatten_reindex {l l' : Level G}
    (h : ∀ o, Level.condition l o → Level.condition l' o) (e : Expr G l) :
    (e.reindex h).flatten = e.flatten := by
  cases e <;> rfl

/-! ## Juxtaposition plumbing

`parseJuxt`/`parseJuxtExtend` build their trees through `Expr.juxtApp`, whose
body carries a transport (`▸`) along `Part.parts_juxt`. These lemmas see through
that transport — `flatten` ignores it, and a juxt `Expr.op` node destructures
back into `juxtApp` form. -/

/-- Flattening ignores a shape transport: the token list a `Parts` flattens to
depends only on its constructors, not on the (propositional) shape index. -/
theorem Parts.flatten_cast {shape shape' : List (Part G)} (h : shape = shape')
    (q : Parts G shape) : (h ▸ q).flatten = q.flatten := by
  cases h; rfl

/-- A shape transport leaves the size unchanged (for the termination measure). -/
theorem Parts.sizeOf_cast {shape shape' : List (Part G)} (h : shape = shape')
    (q : Parts G shape) : sizeOf (h ▸ q) = sizeOf q := by
  cases h; rfl

/-- Transporting a `Parts` forward then back is the identity. -/
theorem Parts.cast_symm {shape shape' : List (Part G)} (h : shape = shape')
    (q : Parts G shape) : h.symm ▸ (h ▸ q) = q := by
  cases h; rfl

/-- The body of a juxt `Expr.op` node decomposes as a left operand `f` and an
argument `x` (modulo the `Part.parts_juxt` transport). The witness equation is
phrased on the *body* so it can drive both the application rewrite and the
`sizeOf` termination measure. -/
theorem Expr.juxt_parts_eq {j : G.Op} (hj : G.operator j = Operator.juxt)
    (parts : Parts G (Part.parts j)) :
    ∃ (f : Expr G (Level.tighterEq j)) (x : Expr G (Level.tighter j)),
      parts = (Part.parts_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil) := by
  have hpe := Part.parts_juxt hj
  have hq : parts = hpe.symm ▸ (hpe ▸ parts) := (Parts.cast_symm hpe parts).symm
  generalize hpe ▸ parts = q at hq
  match q, hq with
  | Parts.hole f (Parts.hole x Parts.nil), hq => exact ⟨f, x, hq⟩

/-- An application node `juxtApp f x` flattens to `f.flatten ++ x.flatten`. -/
@[simp] theorem Expr.flatten_juxtApp {j : G.Op} (hj : G.operator j = Operator.juxt)
    (f : Expr G (Level.tighterEq j)) (x : Expr G (Level.tighter j)) :
    (Expr.juxtApp hj f x).flatten = f.flatten ++ x.flatten := by
  have h : (Expr.juxtApp hj f x).flatten
      = ((Part.parts_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil)).flatten := rfl
  rw [h, Parts.flatten_cast]; simp [Parts.flatten]

/-- Any juxt `Expr.op` node is an application `juxtApp f x`. -/
theorem Expr.op_juxt_eq {j : G.Op} (hj : G.operator j = Operator.juxt)
    (hc : TighterEq G.tighter j j) (parts : Parts G (Part.parts j)) :
    ∃ (f : Expr G (Level.tighterEq j)) (x : Expr G (Level.tighter j)),
      (Expr.op j hc parts : Expr G (Level.tighterEq j)) = Expr.juxtApp hj f x := by
  obtain ⟨f, x, hfx⟩ := Expr.juxt_parts_eq hj parts
  exact ⟨f, x, by rw [hfx]; unfold Expr.juxtApp; congr 1⟩

/-! ## Left-associative-infix plumbing (mirrors the juxtaposition helpers) -/

/-- A left-assoc body's tail (operator tokens + right operand) is nonempty. -/
theorem Part.parts_infxl_tail_ne {o : G.Op} (hl : (G.operator o).isInfxl = true) :
    (Part.parts o).tail ≠ [] := by
  cases hop : G.operator o with
  | infxl tkns => unfold Part.parts; rw [hop]; cases tkns <;> simp
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- The body of a left-assoc `Expr.op` node decomposes as its chaining left
operand `acc` and the tail (parsed segment). -/
theorem Expr.infxl_parts_eq {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (parts : Parts G (Part.parts o)) :
    ∃ (acc : Expr G (Level.tighterEq o)) (tail : Parts G (Part.parts o).tail),
      parts = (Part.parts_infxl_cons hl).symm ▸ Parts.hole acc tail := by
  have hpe := Part.parts_infxl_cons hl
  have hq : parts = hpe.symm ▸ (hpe ▸ parts) := (Parts.cast_symm hpe parts).symm
  generalize hpe ▸ parts = q at hq
  match q, hq with
  | Parts.hole acc tail, hq => exact ⟨acc, tail, hq⟩

/-- A left-assoc fold step flattens to `acc.flatten ++ tail.flatten`. -/
@[simp] theorem Expr.flatten_infxlApp {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (acc : Expr G (Level.tighterEq o)) (tail : Parts G (Part.parts o).tail) :
    (Expr.infxlApp hl acc tail).flatten = acc.flatten ++ tail.flatten := by
  have h : (Expr.infxlApp hl acc tail).flatten
      = ((Part.parts_infxl_cons hl).symm ▸ Parts.hole acc tail).flatten := rfl
  rw [h, Parts.flatten_cast, Parts.flatten_hole]

/-- Any left-assoc `Expr.op` node is a fold step `infxlApp acc tail`. -/
theorem Expr.op_infxl_eq {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (hc : TighterEq G.tighter o o) (parts : Parts G (Part.parts o)) :
    ∃ (acc : Expr G (Level.tighterEq o)) (tail : Parts G (Part.parts o).tail),
      (Expr.op o hc parts : Expr G (Level.tighterEq o)) = Expr.infxlApp hl acc tail := by
  obtain ⟨acc, tail, hat⟩ := Expr.infxl_parts_eq hl parts
  exact ⟨acc, tail, by rw [hat]; unfold Expr.infxlApp; congr 1⟩

/-! ## `RightSublist` lemmas -/

@[simp] theorem RightSublist.list_cons {α : Type _} (a : α) (l : List α) :
    (RightSublist.cons a l).list = l := rfl

@[simp] theorem RightSublist.list_trans {α : Type _} {l : List α}
    (s : RightSublist l) (r : RightSublist s.list) : (s.trans r).list = r.list := rfl

/-! ## Variable-leaf parsing -/

/-- Soundness of `parseVar`: a parsed variable consumes exactly its token. -/
theorem parseVar_sound {l : Level G} {tkns : List Token} {x : Expr G l × RightSublist tkns}
    (hx : x ∈ parseVar l tkns) : x.1.flatten ++ x.2.list = tkns := by
  cases tkns with
  | nil => simp [parseVar] at hx
  | cons t rest =>
      simp only [parseVar] at hx
      split at hx
      · rw [List.mem_singleton] at hx; subst hx; rfl
      · simp at hx

/-- Completeness of `parseVar`: an identifier token is parsed as a variable. -/
theorem parseVar_complete {l : Level G} {t : Token} (hv : G.isVar t = true) (rest : List Token) :
    (Expr.var t hv, RightSublist.cons t rest) ∈ parseVar l (t :: rest) := by
  simp only [parseVar, dif_pos hv]
  exact List.mem_singleton.mpr rfl

/-- A variable is found at *every* level: directly for `loosest`/`tighter`, and via
the fall-through for `tighterEq`. -/
theorem mem_parseExpr_var {l : Level G} {t : Token} (hv : G.isVar t = true) (rest : List Token) :
    (Expr.var t hv, RightSublist.cons t rest) ∈ parseExpr l (t :: rest) := by
  cases l with
  | loosest => rw [parseExpr]; exact List.mem_append_right _ (parseVar_complete hv rest)
  | tighter a => rw [parseExpr]; exact List.mem_append_right _ (parseVar_complete hv rest)
  | tighterEq a =>
      rw [parseExpr]
      by_cases hj : (G.operator a).isJuxt = true
      · -- juxt level: the variable is the lone leftmost atom of an application chain
        simp only [dif_pos hj]
        rw [parseJuxt]
        refine List.mem_flatMap.mpr
          ⟨(Expr.var t hv, RightSublist.cons t rest), ?_, List.mem_cons_self⟩
        rw [parseExpr]
        exact List.mem_append_right _ (parseVar_complete hv rest)
      · simp only [dif_neg hj]
        by_cases hl : (G.operator a).isInfxl = true
        · -- left-assoc level: the variable is the lone leftmost operand
          simp only [dif_pos hl]
          rw [parseInfixL]
          refine List.mem_flatMap.mpr
            ⟨(Expr.var t hv, RightSublist.cons t rest), ?_, List.mem_cons_self⟩
          rw [parseExpr]
          exact List.mem_append_right _ (parseVar_complete hv rest)
        · -- non-left-recursive level: the variable falls through to strictly-tighter
          simp only [dif_neg hl]
          refine List.mem_append_right _
            (List.mem_map.mpr ⟨(Expr.var t hv, RightSublist.cons t rest), ?_, rfl⟩)
          rw [parseExpr]
          exact List.mem_append_right _ (parseVar_complete hv rest)

/-! ## Soundness -/

/-- At a juxtaposition level, `parseExpr` *is* `parseJuxt`. -/
theorem parseExpr_juxt_eq {j : G.Op} (hj : G.operator j = Operator.juxt)
    (tkns : List Token) : parseExpr (Level.tighterEq j) tkns = parseJuxt j hj tkns := by
  rw [parseExpr, dif_pos (show (G.operator j).isJuxt = true by rw [hj]; rfl)]

/-- At a left-associative level, `parseExpr` *is* `parseInfixL`. -/
theorem parseExpr_infxl_eq {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (tkns : List Token) : parseExpr (Level.tighterEq o) tkns = parseInfixL o hl tkns := by
  rw [parseExpr, dif_neg (by simp [Operator.not_isJuxt_of_isInfxl hl]), dif_pos hl]

/-- Joint soundness of the five mutual parser functions: every returned pair
`(tree, leftover)` satisfies `tree.flatten ++ leftover.list = tkns` (for the two
juxtaposition folds, with the accumulator's flattening prepended). One
application of the parser's functional induction principle; each case is
list-membership bookkeeping. -/
theorem parse_sound_all :
    (∀ (l : Level G) (tkns : List Token),
        ∀ x ∈ parseExpr l tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (ps : List (Part G)) (tkns : List Token),
        ∀ x ∈ parseParts ps tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (o : G.Op) (hl : (G.operator o).isInfxl = true) (tkns : List Token),
        ∀ x ∈ parseInfixL o hl tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (o : G.Op) (hl : (G.operator o).isInfxl = true)
        (acc : Expr G (Level.tighterEq o)) (tkns : List Token),
        ∀ x ∈ parseInfixLExtend o hl acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
  ∧ (∀ (j : G.Op) (hj : G.operator j = Operator.juxt) (tkns : List Token),
        ∀ x ∈ parseJuxt j hj tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (j : G.Op) (hj : G.operator j = Operator.juxt)
        (acc : Expr G (Level.tighterEq j)) (tkns : List Token),
        ∀ x ∈ parseJuxtExtend j hj acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
  ∧ ∀ (l : Level G) (cs : List G.Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq G.tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, G.rank c < Level.base l) (tkns : List Token),
      ∀ x ∈ parseExprList l cs h hrank tkns, x.1.flatten ++ x.2.list = tkns := by
  apply parseExpr.mutual_induct
    (motive1 := fun l tkns =>
      ∀ x ∈ parseExpr l tkns, x.1.flatten ++ x.2.list = tkns)
    (motive2 := fun ps tkns =>
      ∀ x ∈ parseParts ps tkns, x.1.flatten ++ x.2.list = tkns)
    (motive3 := fun o hl tkns =>
      ∀ x ∈ parseInfixL o hl tkns, x.1.flatten ++ x.2.list = tkns)
    (motive4 := fun o hl acc tkns =>
      ∀ x ∈ parseInfixLExtend o hl acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
    (motive5 := fun j hj tkns =>
      ∀ x ∈ parseJuxt j hj tkns, x.1.flatten ++ x.2.list = tkns)
    (motive6 := fun j hj acc tkns =>
      ∀ x ∈ parseJuxtExtend j hj acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
    (motive7 := fun l cs h hrank tkns =>
      ∀ x ∈ parseExprList l cs h hrank tkns, x.1.flatten ++ x.2.list = tkns)
  case _ => -- parseExpr .loosest
    intro tkns ih x hx
    rw [parseExpr] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · exact parseVar_sound hx
  case _ => -- parseExpr (.tighter a)
    intro a tkns ih x hx
    rw [parseExpr] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · exact parseVar_sound hx
  case _ => -- parseExpr (.tighterEq a), juxt branch
    intro a tkns hj ihJuxt x hx
    rw [parseExpr_juxt_eq (Operator.eq_juxt hj)] at hx
    exact ihJuxt x hx
  case _ => -- parseExpr (.tighterEq a), left-assoc branch
    intro a tkns _hnj hl ihInfxl x hx
    rw [parseExpr_infxl_eq hl] at hx
    exact ihInfxl x hx
  case _ => -- parseExpr (.tighterEq a), non-left-recursive branch
    intro a tkns hnj hnl ihParts ihTighter x hx
    rw [parseExpr] at hx
    simp only [dif_neg hnj, dif_neg hnl] at hx
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
  case _ => -- parseInfixL
    intro o hl tkns ihExt ihTighter x hx
    rw [parseInfixL] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · -- x is the lone leftmost operand, reindexed
      have := ihTighter p hp
      simpa [Expr.flatten_reindex] using this
    · -- x continues the chain through parseInfixLExtend
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihTighter p hp
      simp only [Expr.flatten_reindex] at h4
      simp only [RightSublist.list_trans]
      rw [h4, h1]
  case _ => -- parseInfixLExtend
    intro o hl acc tkns ihExt ihParts x hx
    rw [parseInfixLExtend] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · -- x folds one tail-segment onto the accumulator
      have h1 := ihParts p hp
      simp only [Expr.flatten_infxlApp, List.append_assoc, h1]
    · -- x continues the chain
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihParts p hp
      simp only [Expr.flatten_infxlApp, List.append_assoc] at h4
      rw [h1] at h4
      simpa [RightSublist.list_trans] using h4
  case _ => -- parseJuxt
    intro j hj tkns ihExt ihTighter x hx
    rw [parseJuxt] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · -- x is the lone leftmost atom, reindexed
      have := ihTighter p hp
      simpa [Expr.flatten_reindex] using this
    · -- x continues the chain through parseJuxtExtend
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihTighter p hp
      simp only [Expr.flatten_reindex] at h4
      simp only [RightSublist.list_trans]
      rw [h4, h1]
  case _ => -- parseJuxtExtend
    intro j hj acc tkns ihExt ihTighter x hx
    rw [parseJuxtExtend] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · -- x folds one argument onto the accumulator
      have h1 := ihTighter p hp
      simp only [Expr.flatten_juxtApp, List.append_assoc, h1]
    · -- x continues the chain
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihTighter p hp
      simp only [Expr.flatten_juxtApp, List.append_assoc] at h4
      rw [h1] at h4
      simpa [RightSublist.list_trans] using h4
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
  cases e <;> rfl

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
  | prefx tkns => simp
  | infx tkns => simp
  | infxl tkns => simp
  | infxr tkns => simp
  | juxt => simp
  | postfx tkns => simp

/-- Extend an established `parseJuxtExtend` result by folding on one more argument:
if `(f, rf)` is reachable and `x` parses from `rf`'s leftover, then `juxtApp f x`
is reachable with the same leftover as `x`. By recursion on the token list. -/
theorem parseJuxtExtend_cont {j : G.Op} (hj : G.operator j = Operator.juxt)
    (acc : Expr G (Level.tighterEq j)) (tkns : List Token)
    (f : Expr G (Level.tighterEq j)) (rf : RightSublist tkns)
    (hf : (f, rf) ∈ parseJuxtExtend j hj acc tkns)
    (x : Expr G (Level.tighter j)) (rx : RightSublist rf.list)
    (hx : (x, rx) ∈ parseExpr (Level.tighter j) rf.list) :
    ∃ r : RightSublist tkns, r.list = rx.list ∧
      (Expr.juxtApp hj f x, r) ∈ parseJuxtExtend j hj acc tkns := by
  rw [parseJuxtExtend] at hf
  obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
  rcases List.mem_cons.mp hf with heq | hmap
  · rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    refine ⟨p.2.trans rx, rfl, ?_⟩
    rw [parseJuxtExtend]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨(Expr.juxtApp hj (Expr.juxtApp hj acc p.1) x, rx), ?_, rfl⟩
    rw [parseJuxtExtend]
    exact List.mem_flatMap.mpr ⟨(x, rx), hx, List.mem_cons_self⟩
  · obtain ⟨z, hz, heq⟩ := List.mem_map.mp hmap
    rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    obtain ⟨r', hr', hm'⟩ :=
      parseJuxtExtend_cont hj (Expr.juxtApp hj acc p.1) p.2.list z.1 z.2 hz x rx hx
    refine ⟨p.2.trans r', hr', ?_⟩
    rw [parseJuxtExtend]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨(Expr.juxtApp hj z.1 x, r'), hm', rfl⟩
  termination_by tkns.length
  decreasing_by exact p.2.length_lt

/-- The same extension step lifted to `parseJuxt`: a chain prefix `(f, rf)` plus an
argument `x` parsed from its leftover yields the extended chain `juxtApp f x`. -/
theorem parseJuxt_cont {j : G.Op} (hj : G.operator j = Operator.juxt)
    {tkns : List Token} {f : Expr G (Level.tighterEq j)} {rf : RightSublist tkns}
    (hf : (f, rf) ∈ parseJuxt j hj tkns)
    {x : Expr G (Level.tighter j)} {rx : RightSublist rf.list}
    (hx : (x, rx) ∈ parseExpr (Level.tighter j) rf.list) :
    ∃ r : RightSublist tkns, r.list = rx.list ∧
      (Expr.juxtApp hj f x, r) ∈ parseJuxt j hj tkns := by
  rw [parseJuxt] at hf
  obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
  rcases List.mem_cons.mp hf with heq | hmap
  · rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    refine ⟨p.2.trans rx, rfl, ?_⟩
    rw [parseJuxt]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨(Expr.juxtApp hj _ x, rx), ?_, rfl⟩
    rw [parseJuxtExtend]
    exact List.mem_flatMap.mpr ⟨(x, rx), hx, List.mem_cons_self⟩
  · obtain ⟨z, hz, heq⟩ := List.mem_map.mp hmap
    rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    obtain ⟨r', hr', hm'⟩ :=
      parseJuxtExtend_cont hj _ p.2.list z.1 z.2 hz x rx hx
    refine ⟨p.2.trans r', hr', ?_⟩
    rw [parseJuxt]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨(Expr.juxtApp hj z.1 x, r'), hm', rfl⟩

/-- Extend an established `parseInfixLExtend` result by one more `∘ rhs` segment
(a `parseParts` of the body tail). Mirrors `parseJuxtExtend_cont`. -/
theorem parseInfixLExtend_cont {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (acc : Expr G (Level.tighterEq o)) (tkns : List Token)
    (f : Expr G (Level.tighterEq o)) (rf : RightSublist tkns)
    (hf : (f, rf) ∈ parseInfixLExtend o hl acc tkns)
    (tp : Parts G (Part.parts o).tail) (rt : RightSublist rf.list)
    (ht : (tp, rt) ∈ parseParts (Part.parts o).tail rf.list) :
    ∃ r : RightSublist tkns, r.list = rt.list ∧
      (Expr.infxlApp hl f tp, r) ∈ parseInfixLExtend o hl acc tkns := by
  rw [parseInfixLExtend] at hf
  obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
  rcases List.mem_cons.mp hf with heq | hmap
  · rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    refine ⟨p.2.trans rt, rfl, ?_⟩
    rw [parseInfixLExtend]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨(Expr.infxlApp hl (Expr.infxlApp hl acc p.1) tp, rt), ?_, rfl⟩
    rw [parseInfixLExtend]
    exact List.mem_flatMap.mpr ⟨(tp, rt), ht, List.mem_cons_self⟩
  · obtain ⟨z, hz, heq⟩ := List.mem_map.mp hmap
    rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    obtain ⟨r', hr', hm'⟩ :=
      parseInfixLExtend_cont hl (Expr.infxlApp hl acc p.1) p.2.list z.1 z.2 hz tp rt ht
    refine ⟨p.2.trans r', hr', ?_⟩
    rw [parseInfixLExtend]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨(Expr.infxlApp hl z.1 tp, r'), hm', rfl⟩
  termination_by tkns.length
  decreasing_by exact p.2.length_lt

/-- The same extension step lifted to `parseInfixL`. Mirrors `parseJuxt_cont`. -/
theorem parseInfixL_cont {o : G.Op} (hl : (G.operator o).isInfxl = true)
    {tkns : List Token} {f : Expr G (Level.tighterEq o)} {rf : RightSublist tkns}
    (hf : (f, rf) ∈ parseInfixL o hl tkns)
    {tp : Parts G (Part.parts o).tail} {rt : RightSublist rf.list}
    (ht : (tp, rt) ∈ parseParts (Part.parts o).tail rf.list) :
    ∃ r : RightSublist tkns, r.list = rt.list ∧
      (Expr.infxlApp hl f tp, r) ∈ parseInfixL o hl tkns := by
  rw [parseInfixL] at hf
  obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
  rcases List.mem_cons.mp hf with heq | hmap
  · rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    refine ⟨p.2.trans rt, rfl, ?_⟩
    rw [parseInfixL]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨(Expr.infxlApp hl _ tp, rt), ?_, rfl⟩
    rw [parseInfixLExtend]
    exact List.mem_flatMap.mpr ⟨(tp, rt), ht, List.mem_cons_self⟩
  · obtain ⟨z, hz, heq⟩ := List.mem_map.mp hmap
    rw [Prod.mk.injEq] at heq
    obtain ⟨hfeq, hrfeq⟩ := heq
    subst hfeq; subst hrfeq
    obtain ⟨r', hr', hm'⟩ :=
      parseInfixLExtend_cont hl _ p.2.list z.1 z.2 hz tp rt ht
    refine ⟨p.2.trans r', hr', ?_⟩
    rw [parseInfixL]
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨(Expr.infxlApp hl z.1 tp, r'), hm', rfl⟩

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
factors through an immediately-tighter candidate, whose rank is smaller. A
juxtaposition level routes through `parseJuxt` instead (`parseJuxt_complete` for
the application node itself, a lone leftmost atom for a strictly-tighter node). -/
theorem parseExpr_tighterEq_complete {a o : G.Op} (hpath : TighterEq G.tighter a o)
    (parts : Parts G (Part.parts o)) (tkns rest : List Token)
    (heq : tkns = parts.flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op o hpath parts : Expr G (.tighterEq a)), r) ∈ parseExpr (.tighterEq a) tkns := by
  by_cases ha : (G.operator a).isJuxt = true
  · -- juxtaposition level
    have haj : G.operator a = Operator.juxt := Operator.eq_juxt ha
    rcases hpath.toTighterOrEq with heqa | hT
    · -- the node is the application itself
      obtain ⟨r, hr, hm⟩ := parseJuxt_complete (heqa ▸ haj) parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      subst heqa
      rw [parseExpr_juxt_eq haj]
      exact hm
    · -- strictly-tighter node: a lone leftmost atom of the chain
      obtain ⟨b, hb, hpath'⟩ := hT.destruct
      obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath' parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      have hmem : ((Expr.op o hpath' parts : Expr G (.tighterEq b)).reindex
          (l := .tighterEq b) (l' := .tighter a)
          (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr (.tighter a) tkns := by
        rw [parseExpr]
        exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) (G.tighter a)
          (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => G.rank_lt hc)
          hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
      rw [parseExpr_juxt_eq haj, parseJuxt]
      exact List.mem_flatMap.mpr ⟨_, hmem, List.mem_cons_self⟩
  · by_cases hl : (G.operator a).isInfxl = true
    · -- left-associative level
      rcases hpath.toTighterOrEq with heqa | hT
      · -- the node is the fold step itself
        obtain ⟨r, hr, hm⟩ := parseInfixL_complete (heqa ▸ hl) parts tkns rest heq
        refine ⟨r, hr, ?_⟩
        subst heqa
        rw [parseExpr_infxl_eq hl]
        exact hm
      · -- strictly-tighter node: a lone leftmost operand of the chain
        obtain ⟨b, hb, hpath'⟩ := hT.destruct
        obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath' parts tkns rest heq
        refine ⟨r, hr, ?_⟩
        have hmem : ((Expr.op o hpath' parts : Expr G (.tighterEq b)).reindex
            (l := .tighterEq b) (l' := .tighter a)
            (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr (.tighter a) tkns := by
          rw [parseExpr]
          exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) (G.tighter a)
            (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => G.rank_lt hc)
            hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
        rw [parseExpr_infxl_eq hl, parseInfixL]
        exact List.mem_flatMap.mpr ⟨_, hmem, List.mem_cons_self⟩
    · -- non-left-recursive level
      rcases hpath.toTighterOrEq with heqa | hT
      · obtain ⟨r, hr, hm⟩ := parseParts_complete parts (Part.parts_ne_nil o) tkns rest heq
        subst heqa
        refine ⟨r, hr, ?_⟩
        rw [parseExpr, dif_neg ha, dif_neg hl]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨(parts, r), hm, rfl⟩)
      · obtain ⟨b, hb, hpath'⟩ := hT.destruct
        obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath' parts tkns rest heq
        refine ⟨r, hr, ?_⟩
        have hmem2 : ((Expr.op o hpath' parts : Expr G (.tighterEq b)).reindex
            (l := .tighterEq b) (l' := .tighter a)
            (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr (.tighter a) tkns := by
          rw [parseExpr]
          exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) (G.tighter a)
            (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => G.rank_lt hc)
            hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
        rw [parseExpr, dif_neg ha, dif_neg hl]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem2, rfl⟩)
termination_by (sizeOf parts, G.rank a + 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.right _ (by have := G.rank_lt hb; omega)
    | exact Prod.Lex.right _ (by omega)

/-- Completeness of `parseJuxt`: an application node `Expr.op j _ parts` (`j`
juxtaposition) is found by the iterative chain parser. The left operand `f` and
argument `x` are parsed by `parseExpr` (smaller bodies), then `parseJuxt_cont`
folds them — so the recursion is on the operator body, not the assembled tree. -/
theorem parseJuxt_complete {j : G.Op} (hj : G.operator j = Operator.juxt)
    (parts : Parts G (Part.parts j)) (tkns rest : List Token)
    (heq : tkns = (Expr.op j TighterEq.refl parts : Expr G (Level.tighterEq j)).flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op j TighterEq.refl parts : Expr G (Level.tighterEq j)), r) ∈ parseJuxt j hj tkns := by
  obtain ⟨f, x, hfx⟩ := Expr.juxt_parts_eq hj parts
  have hop : (Expr.op j TighterEq.refl parts : Expr G (Level.tighterEq j))
      = Expr.juxtApp hj f x := by rw [hfx]; unfold Expr.juxtApp; congr 1
  rw [hop] at heq ⊢
  rw [Expr.flatten_juxtApp] at heq
  obtain ⟨rf, hrf, hmf⟩ :=
    parseExpr_complete f tkns (x.flatten ++ rest) (by rw [heq, List.append_assoc])
  rw [parseExpr_juxt_eq hj] at hmf
  obtain ⟨rx, hrx, hmx⟩ := parseExpr_complete x rf.list rest (by rw [hrf])
  obtain ⟨r, hr, hm⟩ := parseJuxt_cont hj hmf hmx
  exact ⟨r, by rw [hr, hrx], hm⟩
termination_by (sizeOf parts, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    refine Prod.Lex.left _ _ ?_
    have hsz : sizeOf parts = sizeOf (Parts.hole f (Parts.hole x Parts.nil)) := by
      rw [hfx, Parts.sizeOf_cast]
    rw [hsz, Parts.hole.sizeOf_spec, Parts.hole.sizeOf_spec]
    omega

/-- Completeness of `parseInfixL`: a left-assoc fold node `Expr.op o _ parts` is
found by the iterative chain parser. The left operand `acc` and the parsed tail
`tail` are found by `parseExpr` / `parseParts` (smaller bodies), then
`parseInfixL_cont` folds them. Mirrors `parseJuxt_complete`. -/
theorem parseInfixL_complete {o : G.Op} (hl : (G.operator o).isInfxl = true)
    (parts : Parts G (Part.parts o)) (tkns rest : List Token)
    (heq : tkns = (Expr.op o TighterEq.refl parts : Expr G (Level.tighterEq o)).flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op o TighterEq.refl parts : Expr G (Level.tighterEq o)), r) ∈ parseInfixL o hl tkns := by
  obtain ⟨acc, tail, hat⟩ := Expr.infxl_parts_eq hl parts
  have hop : (Expr.op o TighterEq.refl parts : Expr G (Level.tighterEq o))
      = Expr.infxlApp hl acc tail := by rw [hat]; unfold Expr.infxlApp; congr 1
  rw [hop] at heq ⊢
  rw [Expr.flatten_infxlApp] at heq
  obtain ⟨racc, hracc, hmacc⟩ :=
    parseExpr_complete acc tkns (tail.flatten ++ rest) (by rw [heq, List.append_assoc])
  rw [parseExpr_infxl_eq hl] at hmacc
  obtain ⟨rt, hrt, hmt⟩ :=
    parseParts_complete tail (Part.parts_infxl_tail_ne hl) racc.list rest (by rw [hracc])
  obtain ⟨r, hr, hm⟩ := parseInfixL_cont hl hmacc hmt
  exact ⟨r, by rw [hr, hrt], hm⟩
termination_by (sizeOf parts, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    refine Prod.Lex.left _ _ ?_
    have hsz : sizeOf parts = sizeOf (Parts.hole acc tail) := by rw [hat, Parts.sizeOf_cast]
    rw [hsz, Parts.hole.sizeOf_spec]
    omega

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
      exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) (G.tighter a)
        (fun _ hcc _o hco => Tighter.ofMemTighterEq hcc hco) (fun _ hcc => G.rank_lt hcc)
        hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
  | .loosest, .op o hc parts, heq =>
      obtain ⟨a, ha, hpath⟩ := hc
      obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseExpr]
      exact List.mem_append_left _ (parseExprList_complete (l := .loosest) G.loosest
        (fun c hcc _o hco => ⟨c, hcc, hco⟩) (fun _ hcc => G.rank_lt_topRank hcc)
        ha (fun _o hh => ⟨a, ha, hh⟩) hm)
  | l, .var t hv, heq =>
      subst heq
      exact ⟨RightSublist.cons t rest, rfl, mem_parseExpr_var hv rest⟩
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

end LambdaLab.Parser.Mixfix
