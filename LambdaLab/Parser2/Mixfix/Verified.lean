import LambdaLab.Parser2.Mixfix.Parse

/-!
# Correctness of the multi-entry `Part`/`Parts` parser

Three properties on top of `Parse.lean`'s termination:

* **Soundness** (`parseExpr_sound`, `parse_sound`) — every parse consumes
  exactly the tokens it claims: `e.flatten ++ rest.list = tkns`. Proved by the
  parser's own functional induction principle (`parseExpr.mutual_induct`).
* **Completeness** (`parseExpr_complete`, `parse_complete`) — every expression
  is found: `e ∈ parse e.flatten`. Proved by mutual induction on `Expr`/`Parts`
  with an inner descent along the `TighterEq` path (measured by `Entry.rank`).
* **Uniqueness** (`parse_unique`) — reduced to `Grammar.Unambiguous`, the
  grammar-level property that flattening is injective on loosest expressions.
  Soundness pins every full parse's flattening to the input, so unambiguity
  collapses the result list to (copies of) a single tree. Discharging
  `Unambiguous` for a concrete grammar class is a separate (hard) problem.

Everything is threaded through an **entry index** `e : G.Ent`: `parseExpr`,
`Expr`, the precedence levels, the ranks, and the operator bodies all live at a
chosen entry. Cross-entry holes are an ordinary recursive call at the referenced
entry's loosest level, so no extra machinery is needed.
-/

namespace LambdaLab.Parser2.Mixfix

open LambdaLab.Parser2

variable {G : Grammar}

/-! ## Flattening lemmas -/

@[simp] theorem Expr.flatten_op {e : G.Ent} {l : Level (G.entry e)} (o : (G.entry e).Op)
    (hc : Level.condition l o) (parts : Parts G (Operator.body e o)) :
    (Expr.op o hc parts).flatten = parts.flatten := rfl

@[simp] theorem Expr.flatten_var {e : G.Ent} {l : Level (G.entry e)} (t : Token G.isSep)
    (hv : (G.entry e).isVar t = true) :
    (Expr.var (G := G) (e := e) (l := l) t hv).flatten = [t] := rfl

@[simp] theorem Parts.flatten_nil : (Parts.nil (G := G)).flatten = [] := rfl

@[simp] theorem Parts.flatten_hole {e : G.Ent} {l : Level (G.entry e)} {ps : List (Part G)}
    (ex : Expr G e l) (p : Parts G ps) : (Parts.hole ex p).flatten = ex.flatten ++ p.flatten := rfl

@[simp] theorem Parts.flatten_namePart {ps : List (Part G)} (tk : Token G.isSep) (p : Parts G ps) :
    (Parts.namePart tk p).flatten = tk :: p.flatten := rfl

/-- Reindexing only swaps the level-condition proof; the flattening is untouched. -/
@[simp] theorem Expr.flatten_reindex {e : G.Ent} {l l' : Level (G.entry e)}
    (h : ∀ o, Level.condition l o → Level.condition l' o) (ex : Expr G e l) :
    (ex.reindex h).flatten = ex.flatten := by
  cases ex <;> rfl

/-! ## Juxtaposition plumbing

`parseJuxt`/`parseJuxtExtend` build their trees through `Expr.juxtApp`, whose
body carries a transport (`▸`) along `Operator.body_juxt`. These lemmas see through
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
argument `x` (modulo the `Operator.body_juxt` transport). The witness equation is
phrased on the *body* so it can drive both the application rewrite and the
`sizeOf` termination measure. -/
theorem Expr.juxt_parts_eq {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) (parts : Parts G (Operator.body e j)) :
    ∃ (f : Expr G e (Level.tighterEq j)) (x : Expr G e (Level.tighter j)),
      parts = (Operator.body_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil) := by
  have hpe := Operator.body_juxt hj
  have hq : parts = hpe.symm ▸ (hpe ▸ parts) := (Parts.cast_symm hpe parts).symm
  generalize hpe ▸ parts = q at hq
  match q, hq with
  | Parts.hole f (Parts.hole x Parts.nil), hq => exact ⟨f, x, hq⟩

/-- An application node `juxtApp f x` flattens to `f.flatten ++ x.flatten`. -/
@[simp] theorem Expr.flatten_juxtApp {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (f : Expr G e (Level.tighterEq j)) (x : Expr G e (Level.tighter j)) :
    (Expr.juxtApp hj f x).flatten = f.flatten ++ x.flatten := by
  have h : (Expr.juxtApp hj f x).flatten
      = ((Operator.body_juxt hj).symm ▸ Parts.hole f (Parts.hole x Parts.nil)).flatten := rfl
  rw [h, Parts.flatten_cast]; simp [Parts.flatten]

/-- Any juxt `Expr.op` node is an application `juxtApp f x`. -/
theorem Expr.op_juxt_eq {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (hc : TighterEq (G.entry e).tighter j j) (parts : Parts G (Operator.body e j)) :
    ∃ (f : Expr G e (Level.tighterEq j)) (x : Expr G e (Level.tighter j)),
      (Expr.op j hc parts : Expr G e (Level.tighterEq j)) = Expr.juxtApp hj f x := by
  obtain ⟨f, x, hfx⟩ := Expr.juxt_parts_eq hj parts
  exact ⟨f, x, by rw [hfx]; unfold Expr.juxtApp; congr 1⟩

/-! ## Left-associative-infix plumbing (mirrors the juxtaposition helpers) -/

/-- A left-assoc body's tail (operator tokens + right operand) is nonempty. -/
theorem Operator.body_infxl_tail_ne {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) :
    (Operator.body e o).tail ≠ [] := by
  cases hop : (G.entry e).operator o with
  | infxl tkns => unfold Operator.body; rw [hop]; cases tkns <;> simp
  | _ => rw [hop] at hl; simp [Operator.isInfxl] at hl

/-- The body of a left-assoc `Expr.op` node decomposes as its chaining left
operand `acc` and the tail (parsed segment). -/
theorem Expr.infxl_parts_eq {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) (parts : Parts G (Operator.body e o)) :
    ∃ (acc : Expr G e (Level.tighterEq o)) (tail : Parts G (Operator.body e o).tail),
      parts = (Operator.body_infxl_cons hl).symm ▸ Parts.hole acc tail := by
  have hpe := Operator.body_infxl_cons hl
  have hq : parts = hpe.symm ▸ (hpe ▸ parts) := (Parts.cast_symm hpe parts).symm
  generalize hpe ▸ parts = q at hq
  match q, hq with
  | Parts.hole acc tail, hq => exact ⟨acc, tail, hq⟩

/-- A left-assoc fold step flattens to `acc.flatten ++ tail.flatten`. -/
@[simp] theorem Expr.flatten_infxlApp {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    (acc : Expr G e (Level.tighterEq o)) (tail : Parts G (Operator.body e o).tail) :
    (Expr.infxlApp hl acc tail).flatten = acc.flatten ++ tail.flatten := by
  have h : (Expr.infxlApp hl acc tail).flatten
      = ((Operator.body_infxl_cons hl).symm ▸ Parts.hole acc tail).flatten := rfl
  rw [h, Parts.flatten_cast, Parts.flatten_hole]

/-- Any left-assoc `Expr.op` node is a fold step `infxlApp acc tail`. -/
theorem Expr.op_infxl_eq {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    (hc : TighterEq (G.entry e).tighter o o) (parts : Parts G (Operator.body e o)) :
    ∃ (acc : Expr G e (Level.tighterEq o)) (tail : Parts G (Operator.body e o).tail),
      (Expr.op o hc parts : Expr G e (Level.tighterEq o)) = Expr.infxlApp hl acc tail := by
  obtain ⟨acc, tail, hat⟩ := Expr.infxl_parts_eq hl parts
  exact ⟨acc, tail, by rw [hat]; unfold Expr.infxlApp; congr 1⟩

/-! ## `RightSublist` lemmas -/

@[simp] theorem RightSublist.list_cons {α : Type _} (a : α) (l : List α) :
    (RightSublist.cons a l).list = l := rfl

@[simp] theorem RightSublist.list_trans {α : Type _} {l : List α}
    (s : RightSublist l) (r : RightSublist s.list) : (s.trans r).list = r.list := rfl

/-! ## Variable-leaf parsing -/

/-- Soundness of `parseVar`: a parsed variable consumes exactly its token. -/
theorem parseVar_sound {e : G.Ent} {l : Level (G.entry e)} {tkns : List (Token G.isSep)}
    {x : Expr G e l × RightSublist tkns} (hx : x ∈ parseVar e l tkns) :
    x.1.flatten ++ x.2.list = tkns := by
  cases tkns with
  | nil => simp [parseVar] at hx
  | cons t rest =>
      simp only [parseVar] at hx
      split at hx
      · rw [List.mem_singleton] at hx; subst hx; rfl
      · simp at hx

/-- Completeness of `parseVar`: an identifier token is parsed as a variable. -/
theorem parseVar_complete {e : G.Ent} {l : Level (G.entry e)} {t : Token G.isSep}
    (hv : (G.entry e).isVar t = true) (rest : List (Token G.isSep)) :
    (Expr.var t hv, RightSublist.cons t rest) ∈ parseVar e l (t :: rest) := by
  simp only [parseVar, dif_pos hv]
  exact List.mem_singleton.mpr rfl

/-- A variable is found at *every* level: directly for `loosest`/`tighter`, and via
the fall-through for `tighterEq`. -/
theorem mem_parseExpr_var {e : G.Ent} {l : Level (G.entry e)} {t : Token G.isSep}
    (hv : (G.entry e).isVar t = true) (rest : List (Token G.isSep)) :
    (Expr.var t hv, RightSublist.cons t rest) ∈ parseExpr e l (t :: rest) := by
  cases l with
  | loosest => rw [parseExpr]; exact List.mem_append_right _ (parseVar_complete hv rest)
  | tighter a => rw [parseExpr]; exact List.mem_append_right _ (parseVar_complete hv rest)
  | tighterEq a =>
      rw [parseExpr]
      by_cases hj : ((G.entry e).operator a).isJuxt = true
      · -- juxt level: the variable is the lone leftmost atom of an application chain
        simp only [dif_pos hj]
        rw [parseJuxt]
        refine List.mem_flatMap.mpr
          ⟨(Expr.var t hv, RightSublist.cons t rest), ?_, List.mem_cons_self⟩
        rw [parseExpr]
        exact List.mem_append_right _ (parseVar_complete hv rest)
      · simp only [dif_neg hj]
        by_cases hl : ((G.entry e).operator a).isInfxl = true
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
theorem parseExpr_juxt_eq {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt) (tkns : List (Token G.isSep)) :
    parseExpr e (Level.tighterEq j) tkns = parseJuxt e j hj tkns := by
  rw [parseExpr, dif_pos (show ((G.entry e).operator j).isJuxt = true by rw [hj]; rfl)]

/-- At a left-associative level, `parseExpr` *is* `parseInfixL`. -/
theorem parseExpr_infxl_eq {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true) (tkns : List (Token G.isSep)) :
    parseExpr e (Level.tighterEq o) tkns = parseInfixL e o hl tkns := by
  rw [parseExpr, dif_neg (by simp [Operator.not_isJuxt_of_isInfxl hl]), dif_pos hl]

/-- Joint soundness of the seven mutual parser functions: every returned pair
`(tree, leftover)` satisfies `tree.flatten ++ leftover.list = tkns` (for the two
folds, with the accumulator's flattening prepended). One application of the
parser's functional induction principle; each case is list-membership
bookkeeping.

The conjunction is in `parseExpr.mutual_induct` motive order (a canonical order,
*not* the textual mutual order): `parseExpr`, `parseParts`, `parseInfixL`,
`parseInfixLExtend`, `parseJuxt`, `parseJuxtExtend`, `parseExprList`. Everything
is threaded through the entry index `e : G.Ent`. -/
theorem parse_sound_all :
    (∀ (e : G.Ent) (l : Level (G.entry e)) (tkns : List (Token G.isSep)),
        ∀ x ∈ parseExpr e l tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (ps : List (Part G)) (tkns : List (Token G.isSep)),
        ∀ x ∈ parseParts ps tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (e : G.Ent) (o : (G.entry e).Op) (hl : ((G.entry e).operator o).isInfxl = true)
        (tkns : List (Token G.isSep)),
        ∀ x ∈ parseInfixL e o hl tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (e : G.Ent) (o : (G.entry e).Op) (hl : ((G.entry e).operator o).isInfxl = true)
        (acc : Expr G e (Level.tighterEq o)) (tkns : List (Token G.isSep)),
        ∀ x ∈ parseInfixLExtend e o hl acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
  ∧ (∀ (e : G.Ent) (j : (G.entry e).Op) (hj : (G.entry e).operator j = Operator.juxt)
        (tkns : List (Token G.isSep)),
        ∀ x ∈ parseJuxt e j hj tkns, x.1.flatten ++ x.2.list = tkns)
  ∧ (∀ (e : G.Ent) (j : (G.entry e).Op) (hj : (G.entry e).operator j = Operator.juxt)
        (acc : Expr G e (Level.tighterEq j)) (tkns : List (Token G.isSep)),
        ∀ x ∈ parseJuxtExtend e j hj acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
  ∧ ∀ (e : G.Ent) (l : Level (G.entry e)) (cs : List (G.entry e).Op)
      (h : ∀ c ∈ cs, ∀ o, TighterEq (G.entry e).tighter c o → Level.condition l o)
      (hrank : ∀ c ∈ cs, (G.entry e).rank c < Level.base l) (tkns : List (Token G.isSep)),
      ∀ x ∈ parseExprList e l cs h hrank tkns, x.1.flatten ++ x.2.list = tkns := by
  apply parseExpr.mutual_induct
    (motive1 := fun e l tkns =>
      ∀ x ∈ parseExpr e l tkns, x.1.flatten ++ x.2.list = tkns)
    (motive2 := fun ps tkns =>
      ∀ x ∈ parseParts ps tkns, x.1.flatten ++ x.2.list = tkns)
    (motive3 := fun e o hl tkns =>
      ∀ x ∈ parseInfixL e o hl tkns, x.1.flatten ++ x.2.list = tkns)
    (motive4 := fun e o hl acc tkns =>
      ∀ x ∈ parseInfixLExtend e o hl acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
    (motive5 := fun e j hj tkns =>
      ∀ x ∈ parseJuxt e j hj tkns, x.1.flatten ++ x.2.list = tkns)
    (motive6 := fun e j hj acc tkns =>
      ∀ x ∈ parseJuxtExtend e j hj acc tkns, x.1.flatten ++ x.2.list = acc.flatten ++ tkns)
    (motive7 := fun e l cs h hrank tkns =>
      ∀ x ∈ parseExprList e l cs h hrank tkns, x.1.flatten ++ x.2.list = tkns)
  case _ => -- parseExpr .loosest
    intro e tkns ih x hx
    rw [parseExpr] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · exact parseVar_sound hx
  case _ => -- parseExpr (.tighter a)
    intro e a tkns ih x hx
    rw [parseExpr] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · exact parseVar_sound hx
  case _ => -- parseExpr (.tighterEq a), juxt branch
    intro e a tkns hj ihJuxt x hx
    rw [parseExpr_juxt_eq (Operator.eq_juxt hj)] at hx
    exact ihJuxt x hx
  case _ => -- parseExpr (.tighterEq a), left-assoc branch
    intro e a tkns _hnj hl ihInfxl x hx
    rw [parseExpr_infxl_eq hl] at hx
    exact ihInfxl x hx
  case _ => -- parseExpr (.tighterEq a), non-left-recursive branch
    intro e a tkns hnj hnl ihParts ihTighter x hx
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
  case _ => -- parseParts [hole eh lh]
    intro eh lh tkns ih x hx
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
  case _ => -- parseParts (hole eh lh :: y :: rest')
    intro eh lh y rest' tkns ihInner ihExpr x hx
    rw [parseParts] at hx
    obtain ⟨w, hw, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    have h1 := ihExpr w hw
    have h2 := ihInner w z hz
    simp only [Parts.flatten_hole, RightSublist.list_trans, List.append_assoc, h2, h1]
  case _ => -- parseInfixL
    intro e o hl tkns ihExt ihTighter x hx
    rw [parseInfixL] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := ihTighter p hp
      simpa [Expr.flatten_reindex] using this
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihTighter p hp
      simp only [Expr.flatten_reindex] at h4
      simp only [RightSublist.list_trans]
      rw [h4, h1]
  case _ => -- parseInfixLExtend
    intro e o hl acc tkns ihExt ihParts x hx
    rw [parseInfixLExtend] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have h1 := ihParts p hp
      simp only [Expr.flatten_infxlApp, List.append_assoc, h1]
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihParts p hp
      simp only [Expr.flatten_infxlApp, List.append_assoc] at h4
      rw [h1] at h4
      simpa [RightSublist.list_trans] using h4
  case _ => -- parseJuxt
    intro e j hj tkns ihExt ihTighter x hx
    rw [parseJuxt] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := ihTighter p hp
      simpa [Expr.flatten_reindex] using this
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihTighter p hp
      simp only [Expr.flatten_reindex] at h4
      simp only [RightSublist.list_trans]
      rw [h4, h1]
  case _ => -- parseJuxtExtend
    intro e j hj acc tkns ihExt ihTighter x hx
    rw [parseJuxtExtend] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have h1 := ihTighter p hp
      simp only [Expr.flatten_juxtApp, List.append_assoc, h1]
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have h4 := ihExt p z hz
      have h1 := ihTighter p hp
      simp only [Expr.flatten_juxtApp, List.append_assoc] at h4
      rw [h1] at h4
      simpa [RightSublist.list_trans] using h4
  case _ => -- parseExprList l []
    intro e l tkns _ _ _ _ x hx
    rw [parseExprList] at hx
    simp at hx
  case _ => -- parseExprList l (c :: rest)
    intro e l tkns c rest h hrank _ _ ihExpr ihRest x hx
    rw [parseExprList] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa using ihExpr y hy
    · exact ihRest x hx

/-- Soundness of `parseExpr`: a parse at level `l` flattens back to exactly the
consumed prefix. -/
theorem parseExpr_sound {e : G.Ent} {l : Level (G.entry e)} {tkns : List (Token G.isSep)}
    {x : Expr G e l × RightSublist tkns} (hx : x ∈ parseExpr e l tkns) :
    x.1.flatten ++ x.2.list = tkns :=
  parse_sound_all.1 e l tkns x hx

/-- Soundness of `parseParts`. -/
theorem parseParts_sound {ps : List (Part G)} {tkns : List (Token G.isSep)}
    {x : Parts G ps × RightSublist tkns} (hx : x ∈ parseParts ps tkns) :
    x.1.flatten ++ x.2.list = tkns :=
  parse_sound_all.2.1 ps tkns x hx

/-- Soundness of `parse`: a full parse flattens back to the whole input. -/
theorem parse_sound {e : G.Ent} {tkns : List (Token G.isSep)} {ex : Expr G e .loosest}
    (h : ex ∈ parse e tkns) : ex.flatten = tkns := by
  unfold parse at h
  obtain ⟨x, hx, hfm⟩ := List.mem_filterMap.mp h
  split at hfm
  next hnil =>
    cases hfm
    simpa [hnil] using parseExpr_sound hx
  next => cases hfm

/-! ## Completeness -/

/-- Reindexing is independent of the supplied weakening proof. -/
theorem Expr.reindex_irrel {e : G.Ent} {l l' : Level (G.entry e)}
    (h h' : ∀ o, Level.condition l o → Level.condition l' o) (ex : Expr G e l) :
    ex.reindex h = ex.reindex h' := by
  cases ex <;> rfl

/-- A strictly-tighter path decomposes into a first `tighter` step and a
tighter-or-equal remainder. -/
theorem Tighter.destruct {Op : Type} {t : Op → List Op} {a o : Op} (h : Tighter t a o) :
    ∃ b ∈ t a, TighterEq t b o := by
  cases h with
  | base hmem => exact ⟨o, hmem, TighterEq.refl⟩
  | step hmem hT => exact ⟨_, hmem, hT.toTighterEq⟩

theorem Notation.toParts_ne_nil (tkns : Notation G.isSep G.Ent) :
    Notation.toParts (G := G) tkns ≠ [] := by
  cases tkns <;> simp [Notation.toParts]

theorem Operator.body_ne_nil {e : G.Ent} (o : (G.entry e).Op) :
    Operator.body e o ≠ [] := by
  unfold Operator.body
  cases hop : (G.entry e).operator o with
  | closed tkns => exact Notation.toParts_ne_nil tkns
  | prefx tkns => simp
  | infx tkns => simp
  | infxl tkns => simp
  | infxr tkns => simp
  | juxt => simp
  | postfx tkns => simp

/-- Extend an established `parseJuxtExtend` result by folding on one more argument:
if `(f, rf)` is reachable and `x` parses from `rf`'s leftover, then `juxtApp f x`
is reachable with the same leftover as `x`. By recursion on the token list. -/
theorem parseJuxtExtend_cont {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (acc : Expr G e (Level.tighterEq j)) (tkns : List (Token G.isSep))
    (f : Expr G e (Level.tighterEq j)) (rf : RightSublist tkns)
    (hf : (f, rf) ∈ parseJuxtExtend e j hj acc tkns)
    (x : Expr G e (Level.tighter j)) (rx : RightSublist rf.list)
    (hx : (x, rx) ∈ parseExpr e (Level.tighter j) rf.list) :
    ∃ r : RightSublist tkns, r.list = rx.list ∧
      (Expr.juxtApp hj f x, r) ∈ parseJuxtExtend e j hj acc tkns := by
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
theorem parseJuxt_cont {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    {tkns : List (Token G.isSep)} {f : Expr G e (Level.tighterEq j)} {rf : RightSublist tkns}
    (hf : (f, rf) ∈ parseJuxt e j hj tkns)
    {x : Expr G e (Level.tighter j)} {rx : RightSublist rf.list}
    (hx : (x, rx) ∈ parseExpr e (Level.tighter j) rf.list) :
    ∃ r : RightSublist tkns, r.list = rx.list ∧
      (Expr.juxtApp hj f x, r) ∈ parseJuxt e j hj tkns := by
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
theorem parseInfixLExtend_cont {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    (acc : Expr G e (Level.tighterEq o)) (tkns : List (Token G.isSep))
    (f : Expr G e (Level.tighterEq o)) (rf : RightSublist tkns)
    (hf : (f, rf) ∈ parseInfixLExtend e o hl acc tkns)
    (tp : Parts G (Operator.body e o).tail) (rt : RightSublist rf.list)
    (ht : (tp, rt) ∈ parseParts (Operator.body e o).tail rf.list) :
    ∃ r : RightSublist tkns, r.list = rt.list ∧
      (Expr.infxlApp hl f tp, r) ∈ parseInfixLExtend e o hl acc tkns := by
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
theorem parseInfixL_cont {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    {tkns : List (Token G.isSep)} {f : Expr G e (Level.tighterEq o)} {rf : RightSublist tkns}
    (hf : (f, rf) ∈ parseInfixL e o hl tkns)
    {tp : Parts G (Operator.body e o).tail} {rt : RightSublist rf.list}
    (ht : (tp, rt) ∈ parseParts (Operator.body e o).tail rf.list) :
    ∃ r : RightSublist tkns, r.list = rt.list ∧
      (Expr.infxlApp hl f tp, r) ∈ parseInfixL e o hl tkns := by
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
theorem parseExprList_complete {e : G.Ent} {l : Level (G.entry e)} (cs : List (G.entry e).Op)
    (h : ∀ c ∈ cs, ∀ o, TighterEq (G.entry e).tighter c o → Level.condition l o)
    (hrank : ∀ c ∈ cs, (G.entry e).rank c < Level.base l)
    {c : (G.entry e).Op} (hc : c ∈ cs)
    (hcond : ∀ o, Level.condition (Level.tighterEq c) o → Level.condition l o)
    {tkns : List (Token G.isSep)} {ex : Expr G e (.tighterEq c)} {r : RightSublist tkns}
    (hmem : (ex, r) ∈ parseExpr e (.tighterEq c) tkns) :
    (ex.reindex hcond, r) ∈ parseExprList e l cs h hrank tkns := by
  induction cs with
  | nil => cases hc
  | cons c' rest ih =>
      rw [parseExprList]
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact List.mem_append_left _ (List.mem_map.mpr
          ⟨(ex, r), hmem, congrArg (fun t => (t, r)) (Expr.reindex_irrel _ hcond ex)⟩)
      · exact List.mem_append_right _ (ih _ _ hc')

mutual

/-- Completeness of `parseParts`: a body inhabitant `p : Parts G ps` is found in
`parseParts ps` on its own flattening (any right-extension `rest`), leaving
exactly `rest`. (`ps = []` is excluded: `parseParts [] = []` by design, so the
parser never produces the empty-consuming `Parts.nil` on its own.) -/
theorem parseParts_complete {ps : List (Part G)} (p : Parts G ps) (hps : ps ≠ [])
    (tkns rest : List (Token G.isSep)) (heq : tkns = p.flatten ++ rest) :
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
  | [.hole _ _], .hole ex .nil, heq =>
      simp only [Parts.flatten_hole, Parts.flatten_nil, List.append_nil] at heq
      obtain ⟨r, hr, hm⟩ := parseExpr_complete ex tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseParts]
      exact List.mem_map.mpr ⟨(ex, r), hm, rfl⟩
  | .namePart tk :: y :: rest', .namePart _ p', heq =>
      simp only [Parts.flatten_namePart, List.cons_append] at heq
      subst heq
      obtain ⟨r₂, hr₂, hm₂⟩ :=
        parseParts_complete p' (List.cons_ne_nil y rest') (p'.flatten ++ rest) rest rfl
      refine ⟨(RightSublist.cons tk (p'.flatten ++ rest)).trans r₂, by simp [hr₂], ?_⟩
      rw [parseParts, if_pos rfl]
      exact List.mem_map.mpr ⟨(p', r₂), hm₂, rfl⟩
  | .hole _ _ :: y :: rest', .hole ex p', heq =>
      simp only [Parts.flatten_hole, List.append_assoc] at heq
      obtain ⟨r₁, hr₁, hm₁⟩ :=
        parseExpr_complete ex tkns (p'.flatten ++ rest) heq
      obtain ⟨r₂, hr₂, hm₂⟩ :=
        parseParts_complete p' (List.cons_ne_nil y rest') r₁.list rest hr₁
      refine ⟨r₁.trans r₂, by simp [hr₂], ?_⟩
      rw [parseParts]
      exact List.mem_flatMap.mpr ⟨(ex, r₁), hm₁, List.mem_map.mpr ⟨(p', r₂), hm₂, rfl⟩⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals simp_wf
  all_goals exact Prod.Lex.left _ _ (by first | (simp; omega) | omega)

/-- Completeness at a `tighterEq` level, by descent along the `TighterEq` path:
either the path is trivial and the operator's own body parse applies, or it
factors through an immediately-tighter candidate, whose rank is smaller. A
juxtaposition level routes through `parseJuxt` instead (`parseJuxt_complete` for
the application node itself, a lone leftmost atom for a strictly-tighter node). -/
theorem parseExpr_tighterEq_complete {e : G.Ent} {a o : (G.entry e).Op}
    (hpath : TighterEq (G.entry e).tighter a o)
    (parts : Parts G (Operator.body e o)) (tkns rest : List (Token G.isSep))
    (heq : tkns = parts.flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op o hpath parts : Expr G e (.tighterEq a)), r) ∈ parseExpr e (.tighterEq a) tkns := by
  by_cases ha : ((G.entry e).operator a).isJuxt = true
  · -- juxtaposition level
    have haj : (G.entry e).operator a = Operator.juxt := Operator.eq_juxt ha
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
      have hmem : ((Expr.op o hpath' parts : Expr G e (.tighterEq b)).reindex
          (l := .tighterEq b) (l' := .tighter a)
          (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr e (.tighter a) tkns := by
        rw [parseExpr]
        exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) ((G.entry e).tighter a)
          (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => (G.entry e).rank_lt hc)
          hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
      rw [parseExpr_juxt_eq haj, parseJuxt]
      exact List.mem_flatMap.mpr ⟨_, hmem, List.mem_cons_self⟩
  · by_cases hl : ((G.entry e).operator a).isInfxl = true
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
        have hmem : ((Expr.op o hpath' parts : Expr G e (.tighterEq b)).reindex
            (l := .tighterEq b) (l' := .tighter a)
            (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr e (.tighter a) tkns := by
          rw [parseExpr]
          exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) ((G.entry e).tighter a)
            (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => (G.entry e).rank_lt hc)
            hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
        rw [parseExpr_infxl_eq hl, parseInfixL]
        exact List.mem_flatMap.mpr ⟨_, hmem, List.mem_cons_self⟩
    · -- non-left-recursive level
      rcases hpath.toTighterOrEq with heqa | hT
      · obtain ⟨r, hr, hm⟩ := parseParts_complete parts (Operator.body_ne_nil o) tkns rest heq
        subst heqa
        refine ⟨r, hr, ?_⟩
        rw [parseExpr, dif_neg ha, dif_neg hl]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨(parts, r), hm, rfl⟩)
      · obtain ⟨b, hb, hpath'⟩ := hT.destruct
        obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath' parts tkns rest heq
        refine ⟨r, hr, ?_⟩
        have hmem2 : ((Expr.op o hpath' parts : Expr G e (.tighterEq b)).reindex
            (l := .tighterEq b) (l' := .tighter a)
            (fun _o hh => Tighter.ofMemTighterEq hb hh), r) ∈ parseExpr e (.tighter a) tkns := by
          rw [parseExpr]
          exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) ((G.entry e).tighter a)
            (fun _ hc _o hco => Tighter.ofMemTighterEq hc hco) (fun _ hc => (G.entry e).rank_lt hc)
            hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
        rw [parseExpr, dif_neg ha, dif_neg hl]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem2, rfl⟩)
termination_by (sizeOf parts, (G.entry e).rank a + 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.right _ (by have := (G.entry e).rank_lt hb; omega)
    | exact Prod.Lex.right _ (by omega)

/-- Completeness of `parseJuxt`: an application node `Expr.op j _ parts` (`j`
juxtaposition) is found by the iterative chain parser. The left operand `f` and
argument `x` are parsed by `parseExpr` (smaller bodies), then `parseJuxt_cont`
folds them — so the recursion is on the operator body, not the assembled tree. -/
theorem parseJuxt_complete {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (parts : Parts G (Operator.body e j)) (tkns rest : List (Token G.isSep))
    (heq : tkns = (Expr.op j TighterEq.refl parts : Expr G e (Level.tighterEq j)).flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op j TighterEq.refl parts : Expr G e (Level.tighterEq j)), r)
        ∈ parseJuxt e j hj tkns := by
  obtain ⟨f, x, hfx⟩ := Expr.juxt_parts_eq hj parts
  have hop : (Expr.op j TighterEq.refl parts : Expr G e (Level.tighterEq j))
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
theorem parseInfixL_complete {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    (parts : Parts G (Operator.body e o)) (tkns rest : List (Token G.isSep))
    (heq : tkns = (Expr.op o TighterEq.refl parts : Expr G e (Level.tighterEq o)).flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧
      ((Expr.op o TighterEq.refl parts : Expr G e (Level.tighterEq o)), r)
        ∈ parseInfixL e o hl tkns := by
  obtain ⟨acc, tail, hat⟩ := Expr.infxl_parts_eq hl parts
  have hop : (Expr.op o TighterEq.refl parts : Expr G e (Level.tighterEq o))
      = Expr.infxlApp hl acc tail := by rw [hat]; unfold Expr.infxlApp; congr 1
  rw [hop] at heq ⊢
  rw [Expr.flatten_infxlApp] at heq
  obtain ⟨racc, hracc, hmacc⟩ :=
    parseExpr_complete acc tkns (tail.flatten ++ rest) (by rw [heq, List.append_assoc])
  rw [parseExpr_infxl_eq hl] at hmacc
  obtain ⟨rt, hrt, hmt⟩ :=
    parseParts_complete tail (Operator.body_infxl_tail_ne hl) racc.list rest (by rw [hracc])
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

/-- Completeness of `parseExpr`: every `ex : Expr G e l` is found on its own
flattening (any right-extension `rest`), leaving exactly `rest`. -/
theorem parseExpr_complete {e : G.Ent} {l : Level (G.entry e)} (ex : Expr G e l)
    (tkns rest : List (Token G.isSep)) (heq : tkns = ex.flatten ++ rest) :
    ∃ r : RightSublist tkns, r.list = rest ∧ (ex, r) ∈ parseExpr e l tkns := by
  match l, ex, heq with
  | .tighterEq a, .op o hc parts, heq =>
      exact parseExpr_tighterEq_complete hc parts tkns rest heq
  | .tighter a, .op o hc parts, heq =>
      obtain ⟨b, hb, hpath⟩ := Tighter.destruct hc
      obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseExpr]
      exact List.mem_append_left _ (parseExprList_complete (l := .tighter a) ((G.entry e).tighter a)
        (fun _ hcc _o hco => Tighter.ofMemTighterEq hcc hco) (fun _ hcc => (G.entry e).rank_lt hcc)
        hb (fun _o hh => Tighter.ofMemTighterEq hb hh) hm)
  | .loosest, .op o hc parts, heq =>
      obtain ⟨a, ha, hpath⟩ := hc
      obtain ⟨r, hr, hm⟩ := parseExpr_tighterEq_complete hpath parts tkns rest heq
      refine ⟨r, hr, ?_⟩
      rw [parseExpr]
      exact List.mem_append_left _ (parseExprList_complete (l := .loosest) (G.entry e).loosest
        (fun c hcc _o hco => ⟨c, hcc, hco⟩) (fun _ hcc => (G.entry e).rank_lt_topRank hcc)
        ha (fun _o hh => ⟨a, ha, hh⟩) hm)
  | l, .var t hv, heq =>
      subst heq
      exact ⟨RightSublist.cons t rest, rfl, mem_parseExpr_var hv rest⟩
termination_by (sizeOf ex, 0)
decreasing_by
  all_goals simp_wf
  all_goals exact Prod.Lex.left _ _ (by first | (simp; omega) | omega)

end

/-- Completeness of `parse`: every loosest expression is a full parse of its
own flattening. -/
theorem parse_complete {e : G.Ent} (ex : Expr G e .loosest) : ex ∈ parse e ex.flatten := by
  obtain ⟨r, hr, hm⟩ := parseExpr_complete ex ex.flatten [] (by simp)
  unfold parse
  exact List.mem_filterMap.mpr ⟨(ex, r), hm, by simp [hr]⟩

/-- The full characterization of `parse` as a set: its members are exactly the
loosest expressions flattening to the input. (Soundness + completeness.) -/
theorem mem_parse_iff {e : G.Ent} {tkns : List (Token G.isSep)} {ex : Expr G e .loosest} :
    ex ∈ parse e tkns ↔ ex.flatten = tkns :=
  ⟨parse_sound, fun h => h ▸ parse_complete ex⟩

/-! ## Uniqueness -/

/-- A grammar entry `e` is **unambiguous** when flattening is injective on its
loosest expressions: no token string is the flattening of two distinct trees.
This is a property of the *grammar*, not the parser — by `mem_parse_iff` the
parser returns exactly the trees flattening to the input, so unambiguity is
precisely what collapses the result list to copies of a single tree. Discharging
it for a concrete grammar (class) is a separate problem. -/
def Grammar.Unambiguous (G : Grammar) (e : G.Ent) : Prop :=
  ∀ (e₁ e₂ : Expr G e .loosest), e₁.flatten = e₂.flatten → e₁ = e₂

/-- Uniqueness of full parses, conditional on entry unambiguity: any two
members of `parse e tkns` are equal (the list may still contain duplicates when
the precedence DAG reaches an operator along several paths). -/
theorem parse_unique {e : G.Ent} (hG : G.Unambiguous e) {tkns : List (Token G.isSep)}
    {e₁ e₂ : Expr G e .loosest} (h₁ : e₁ ∈ parse e tkns) (h₂ : e₂ ∈ parse e tkns) :
    e₁ = e₂ :=
  hG e₁ e₂ ((parse_sound h₁).trans (parse_sound h₂).symm)

end LambdaLab.Parser2.Mixfix
