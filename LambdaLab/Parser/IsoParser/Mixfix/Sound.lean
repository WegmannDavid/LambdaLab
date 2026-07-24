import LambdaLab.Parser.IsoParser.Mixfix.Parse

/-!
# Parser soundness (exactness): a parse flattens back to the consumed input

`parseExpr e l tkns = some (t, s)` implies `t.flatten ++ s.list = tkns` — whatever the parser
consumed, `flatten` reproduces exactly. This is the exactness half of the round-trip (the
`print_parse` law of the eventual `IsoParser`), proved by functional induction over the mutual
well-founded parser. It needs no grammar side-conditions — exactness is unconditional.

Ported in shape from the `CBiparser` proof, adapted to the abstract token alphabet.
-/

namespace LambdaLab.Parser.IsoParser.Mixfix

variable {Tok : Type} {G : Grammar Tok}

/-- The variable leaf is sound: it consumes exactly the one variable token it returns. -/
theorem parseVar_sound (e : G.Ent) (l : Level (G.entry e)) (tkns : List Tok)
    {t : Expr G e l} {s : RightSublist tkns} (h : parseVar e l tkns = some (t, s)) :
    t.flatten ++ s.list = tkns := by
  cases tkns with
  | nil => simp [parseVar] at h
  | cons hd tl =>
      simp only [parseVar] at h
      split at h
      · rename_i hv
        obtain ⟨rfl, rfl⟩ := Option.some.inj h
        simp [Expr.flatten]
      · exact absurd h (by simp)

/-! ## How `flatten` sees the tree-builders (casts over the shape index are invisible). -/

theorem Parts.flatten_cast {s s' : List (Part G)} (h : s = s') (ps : Parts G s) :
    (h ▸ ps).flatten = ps.flatten := by subst h; rfl

@[simp] theorem Expr.reindex_flatten {e : G.Ent} {l l' : Level (G.entry e)}
    (h : ∀ o, Level.condition l o → Level.condition l' o) (x : Expr G e l) :
    (x.reindex h).flatten = x.flatten := by
  cases x <;> rfl

@[simp] theorem Expr.juxtApp_flatten {e : G.Ent} {j : (G.entry e).Op}
    (hj : (G.entry e).operator j = Operator.juxt)
    (f : Expr G e (Level.tighterEq j)) (x : Expr G e (Level.tighter j)) :
    (Expr.juxtApp hj f x).flatten = f.flatten ++ x.flatten := by
  simp [Expr.juxtApp, Expr.flatten, Parts.flatten_cast, Parts.flatten]

@[simp] theorem Expr.infxlApp_flatten {e : G.Ent} {o : (G.entry e).Op}
    (hl : ((G.entry e).operator o).isInfxl = true)
    (acc : Expr G e (Level.tighterEq o)) (tail : Parts G (Operator.body e o).tail) :
    (Expr.infxlApp hl acc tail).flatten = acc.flatten ++ tail.flatten := by
  simp [Expr.infxlApp, Expr.flatten, Parts.flatten_cast, Parts.flatten]

/-- Case on an `orElse` without generalising its arguments away. -/
theorem orElse_eq_some {α : Type _} (a : Option α) (b : Unit → Option α) (x : α) :
    (a.orElse b) = some x ↔ a = some x ∨ (a = none ∧ b () = some x) := by
  cases a <;> simp [Option.orElse]

/-- A longest-match result came from one of the two candidates. -/
theorem longer_eq_some {α : Type} {tkns : List Tok}
    {a b : Option (α × RightSublist tkns)} {x : α × RightSublist tkns}
    (h : longer a b = some x) : a = some x ∨ b = some x := by
  cases a with
  | none => right; simpa [longer] using h
  | some p =>
      cases b with
      | none => left; simpa [longer] using h
      | some q =>
          simp only [longer] at h
          split at h
          · right; exact h
          · left; exact h

variable [inst : DecidableEq Tok]

-- The catch-all `first | …` induction block below applies simp lemma sets that are only partly
-- used in whichever alternative fires; the resulting "unused simp arg" reports are noise.
set_option linter.unusedSimpArgs false

/-- **Soundness**, all seven mutually-recursive functions at once. The two accumulator-carrying
folds satisfy a **shifted** statement (result flattens to accumulator ++ consumed).

The motives pin the `DecidableEq` instance with `@`: `parseExpr.induct`'s motive IHs otherwise leave
it a higher-order metavar that won't unify with the ambient one. -/
theorem parseExpr_sound (e : G.Ent) (l : Level (G.entry e)) (tkns : List Tok) :
    ∀ (t : Expr G e l) (s : RightSublist tkns),
      parseExpr e l tkns = some (t, s) → t.flatten ++ s.list = tkns := by
  induction e, l, tkns using parseExpr.induct
    (motive2 := fun ps tkns =>
      ∀ p s, @parseParts Tok inst G ps tkns = some (p, s) → p.flatten ++ s.list = tkns)
    (motive3 := fun e o hl tkns =>
      ∀ t s, @parseInfixL Tok inst G e o hl tkns = some (t, s) → t.flatten ++ s.list = tkns)
    (motive4 := fun e o hl acc tkns =>
      ∀ t s, @parseInfixLExtend Tok inst G e o hl acc tkns = some (t, s) →
        t.flatten ++ s.list = acc.flatten ++ tkns)
    (motive5 := fun e j hj tkns =>
      ∀ t s, @parseJuxt Tok inst G e j hj tkns = some (t, s) → t.flatten ++ s.list = tkns)
    (motive6 := fun e j hj acc tkns =>
      ∀ t s, @parseJuxtExtend Tok inst G e j hj acc tkns = some (t, s) →
        t.flatten ++ s.list = acc.flatten ++ tkns)
    (motive7 := fun e l cs h hrank tkns =>
      ∀ t s, @parseExprList Tok inst G e l cs h hrank tkns = some (t, s) → t.flatten ++ s.list = tkns)
  case case5 e tkns a hj hl ihExpr ihParts =>
    intro t s heq
    rw [parseExpr] at heq
    rw [dif_neg hj, dif_neg hl] at heq
    dsimp only at heq
    rw [orElse_eq_some] at heq
    rcases heq with h | ⟨_, h⟩
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨xp, xs⟩, hx, rfl, rfl⟩ := h
      simpa [Expr.flatten] using ihParts xp xs hx
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨xp, xs⟩, hx, rfl, rfl⟩ := h
      simpa using ihExpr xp xs hx
  case case15 =>
    intros; rename_i ha
    rw [parseInfixL] at ha
    simp_all (config := { zetaDelta := true })
    try (obtain ⟨rfl, rfl⟩ := ha; simp_all (config := { zetaDelta := true }))
  case case16 =>
    intros; rename_i ha
    rw [parseInfixL] at ha
    simp_all (config := { zetaDelta := true })
    try (obtain ⟨rfl, rfl⟩ := ha; simp_all (config := { zetaDelta := true }))
  case case17 =>
    intros; rename_i ha
    rw [parseInfixL] at ha
    simp_all (config := { zetaDelta := true })
    try (obtain ⟨rfl, rfl⟩ := ha; simp_all (config := { zetaDelta := true }))
  case case21 =>
    intros; rename_i ha
    rw [parseJuxt] at ha
    simp_all (config := { zetaDelta := true })
    try (obtain ⟨rfl, rfl⟩ := ha; simp_all (config := { zetaDelta := true }))
  case case22 =>
    intros; rename_i ha
    rw [parseJuxt] at ha
    simp_all (config := { zetaDelta := true })
    try (obtain ⟨rfl, rfl⟩ := ha; simp_all (config := { zetaDelta := true }))
  case case23 =>
    intros; rename_i ha
    rw [parseJuxt] at ha
    simp_all (config := { zetaDelta := true })
    try (obtain ⟨rfl, rfl⟩ := ha; simp_all (config := { zetaDelta := true }))
  case case14 e l y rest' tkns ihExpr ihParts p s heq =>
    rw [parseParts] at heq
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at heq
    obtain ⟨x, hx, z, hz, rfl, rfl⟩ := heq
    have h1 := ihParts x z.1 z.2 hz
    have h2 := ihExpr x.1 x.2 hx
    simp only [Parts.flatten, RightSublist.trans_list, List.append_assoc, h1, h2]
  all_goals intros
  all_goals first
    | done
    | (simp_all [parseParts, parseExprList, parseVar, Expr.flatten, Parts.flatten]; done)
    | (rename_i heq
       rw [parseExprList] at heq
       rcases longer_eq_some heq with h | h <;>
         first
           | (simp_all [parseVar, Expr.flatten, Parts.flatten, List.append_assoc]; done)
           | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff, Prod.mk.injEq] at h
              obtain ⟨x, hx, rfl, rfl⟩ := h
              simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
              done)
           | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
              obtain ⟨x, hx, rfl⟩ := h
              simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
              done))
    | (rename_i heq
       rw [parseExpr] at heq
       rw [orElse_eq_some] at heq
       rcases heq with h | ⟨_, h⟩ <;>
         first
           | (exact parseVar_sound _ _ _ h)
           | (simp_all [parseVar, Expr.flatten, Parts.flatten, List.append_assoc]; done)
           | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff, Prod.mk.injEq] at h
              obtain ⟨x, hx, rfl, rfl⟩ := h
              simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
              done)
           | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
              obtain ⟨x, hx, rfl⟩ := h
              simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
              done))
    | (rename_i heq
       first
         | rw [parseParts] at heq
         | rw [parseJuxtExtend] at heq
         | rw [parseInfixLExtend] at heq
         | rw [parseExprList] at heq
         | rw [parseExpr] at heq
         | rw [parseJuxt] at heq
         | rw [parseInfixL] at heq
       first
         | (simp_all [parseVar, Expr.flatten, Parts.flatten, List.append_assoc]; done)
         | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heq
            obtain ⟨x, hx, rfl⟩ := heq
            simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
            done)
         | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff, Prod.mk.injEq] at heq
            obtain ⟨x, hx, y, hy, rfl, rfl⟩ := heq
            simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
            done)
         | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heq
            obtain ⟨x, hx, y, hy, rfl⟩ := heq
            simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
            done)
         | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heq
            obtain ⟨a, b, hab, rfl, rfl⟩ := heq
            simp_all [Expr.flatten, Parts.flatten, List.append_assoc]
            done)
         | (simp_all (config := { zetaDelta := true })
              [parseVar, Expr.flatten, Parts.flatten, List.append_assoc]
            try (obtain ⟨rfl, rfl⟩ := heq
                 simp_all (config := { zetaDelta := true })
                   [parseVar, Expr.flatten, Parts.flatten, List.append_assoc])
            done)
         | (split at heq <;>
              first
                | (simp at heq; done)
                | (simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heq
                   obtain ⟨a, b, hab, rfl, rfl⟩ := heq
                   simp_all [Expr.flatten, Parts.flatten, List.append_assoc])
                | (simp_all [parseVar, Expr.flatten, Parts.flatten, List.append_assoc]; done)))

end LambdaLab.Parser.IsoParser.Mixfix
