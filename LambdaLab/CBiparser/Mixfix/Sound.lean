import LambdaLab.CBiparser.Mixfix.Parse

/-!
# Parser soundness: a parse flattens back to the consumed input

`parseExpr e l tkns = some (t, s)` implies `t.flatten ++ s.list = tkns` — the tree the
parser returns, flattened, is exactly the prefix it consumed (with `s.list` the leftover).
This is the *soundness* half of the round-trip: the parser never fabricates or drops
tokens. Combined with determinism it gives uniqueness; the *completeness* half — that
`print`ing a tree and parsing it back recovers the tree — is proved separately (it needs
the greedy "FOLLOW" side-condition, the generic form of `Concrete`'s `rest.head? ≠ '+'`).

Proof machinery this file establishes (reused by completeness): induction over the
well-founded parser recursion, and the `flatten`/`++`/`RightSublist.list` bookkeeping.
-/

namespace LambdaLab.CBiparser.Mixfix

variable {G : Grammar}

/-- The variable leaf is sound: it consumes exactly the one variable token it returns. -/
theorem parseVar_sound (e : G.Ent) (l : Level (G.entry e)) (tkns : List (Token G.isSep))
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

/-! ## How `flatten` sees the tree-builders

The parser builds nodes with `reindex`, `juxtApp` and `infxlApp`, each of which casts over the
*shape* index (`▸`). `flatten` doesn't care about the index — it is determined by the
constructors — but `simp` can't see that through a cast. These four lemmas say so, and they are
what turns the induction from 19 open cases into an automated one. -/

/-- A cast over the shape index is invisible to `flatten`. -/
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

/-- Case on an `orElse` **without generalising its arguments away**. A bare `split` on
`Option.orElse` abstracts the two alternatives into opaque variables, severing the link to
`parseExpr`/`parseExprList` — and then no induction hypothesis can apply. -/
theorem orElse_eq_some {α : Type _} (a : Option α) (b : Unit → Option α) (x : α) :
    (a.orElse b) = some x ↔ a = some x ∨ (a = none ∧ b () = some x) := by
  cases a <;> simp [Option.orElse]

/-- The `longer` analogue of `orElse_eq_some`: a longest-match result came from one of the two
candidates. That is all soundness needs — *which* one won is a completeness question. -/
theorem longer_eq_some {α : Type} {tkns : List (Token G.isSep)}
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

/-- **Soundness**, all seven mutually-recursive functions at once.

The delicate part is the *motives*. The two accumulator-carrying folds (`parseJuxtExtend`,
`parseInfixLExtend`) satisfy a **shifted** statement: what they return flattens to the
accumulator's flattening **followed by** the tokens they consumed. Stated unshifted, the
induction cannot close — the fold has already absorbed the accumulator into its result. -/
theorem parseExpr_sound (e : G.Ent) (l : Level (G.entry e)) (tkns : List (Token G.isSep)) :
    ∀ (t : Expr G e l) (s : RightSublist tkns),
      parseExpr e l tkns = some (t, s) → t.flatten ++ s.list = tkns := by
  induction e, l, tkns using parseExpr.induct
    (motive2 := fun ps tkns =>
      ∀ p s, parseParts ps tkns = some (p, s) → p.flatten ++ s.list = tkns)
    (motive3 := fun e o hl tkns =>
      ∀ t s, parseInfixL e o hl tkns = some (t, s) → t.flatten ++ s.list = tkns)
    (motive4 := fun e o hl acc tkns =>
      ∀ t s, parseInfixLExtend e o hl acc tkns = some (t, s) →
        t.flatten ++ s.list = acc.flatten ++ tkns)
    (motive5 := fun e j hj tkns =>
      ∀ t s, parseJuxt e j hj tkns = some (t, s) → t.flatten ++ s.list = tkns)
    (motive6 := fun e j hj acc tkns =>
      ∀ t s, parseJuxtExtend e j hj acc tkns = some (t, s) →
        t.flatten ++ s.list = acc.flatten ++ tkns)
    (motive7 := fun e l cs h hrank tkns =>
      ∀ t s, parseExprList e l cs h hrank tkns = some (t, s) → t.flatten ++ s.list = tkns)
  -- **The operator fall-through.** A nested `dite` (juxt? infxl?), then a `let`, then an
  -- `orElse` of two `map`s: try the operator's parts; failing that, drop to the tighter level
  -- and `reindex`. No general tactic threads this — written out.
  case case5 e tkns a hj hl ihExpr ihParts =>
    intro t s heq
    rw [parseExpr] at heq
    rw [dif_neg hj, dif_neg hl] at heq
    dsimp only at heq
    rw [orElse_eq_some] at heq
    rcases heq with h | ⟨_, h⟩
    · -- the operator's parts parsed
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨x, hx, rfl, rfl⟩ := h
      simpa [Expr.flatten] using ihParts x.1 x.2 hx
    · -- fell through to the tighter level
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨x, hx, rfl, rfl⟩ := h
      simpa using ihExpr x.1 x.2 hx
  -- **`parseInfixL` / `parseJuxt`.** The induction principle has *already* split their two
  -- nested matches, so the branch equations (`parseExpr … = none`, `…Extend … = some …`) sit
  -- in the context — no manual splitting is needed or wanted. Two subtleties: `zetaDelta` is
  -- required because the left operand `lone` is a **`let`-bound fvar** that `simp` will not
  -- otherwise unfold (so it cannot see `lone.flatten = x.flatten` via `reindex_flatten`); and
  -- `simp_all` leaves the result equation as an unsubstituted conjunction, so destructure it.
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
  -- **A hole part followed by more parts.** `parseExpr` binds, then `parseParts` maps; the two
  -- IHs compose across a re-association (`(a ++ b) ++ c = a ++ (b ++ c)`), which is the only
  -- place `List.append_assoc` is load-bearing.
  case case14 e l y rest' tkns ihExpr ihParts p s heq =>
    rw [parseParts] at heq
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at heq
    obtain ⟨x, hx, z, hz, rfl, rfl⟩ := heq
    have h1 := ihParts x z.1 z.2 hz     -- z.1.flatten ++ z.2.list = x.2.list
    have h2 := ihExpr x.1 x.2 hx        -- x.1.flatten ++ x.2.list = tkns
    simp only [Parts.flatten, RightSublist.trans_list, List.append_assoc, h1, h2]
  -- Everything else: unfold ITS OWN parse function exactly once (they are mutually recursive,
  -- so `simp` must never unfold them — it would loop), then normalise the `orElse` / `map` /
  -- `match` that exposes, and let the IHs plus the flatten lemmas finish.
  all_goals intros
  all_goals first
    | done
    | (simp_all [parseParts, parseExprList, parseVar, Expr.flatten, Parts.flatten]; done)
    -- `parseExprList` now takes the LONGEST match, not the first success.
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

end LambdaLab.CBiparser.Mixfix
