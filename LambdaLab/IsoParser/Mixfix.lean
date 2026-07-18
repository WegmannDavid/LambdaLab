import LambdaLab.IsoParser.Basic
import LambdaLab.CBiparser.Mixfix.Complete

/-!
# The mixfix parser, migrated to `IsoParser`

The whole mixfix development (grammar, `Expr`/`flatten`, the parse algorithm, soundness, unambiguity)
depends only on `Token`, not on the `CBiparser` wrapper — so it is **reused**, not cloned. Only the
wrapper changes: `mixfix` packages `parseCB` + `Expr.flatten` as an `IsoParser`.

The grammar is unambiguous, so the tree pins its token string — **no choice** — hence the annotation
is trivial (`fun _ => PUnit`). The two `IsoParser` laws land on existing lemmas:

* `print_parse` (parse consumed exactly what `flatten` prints) = `parseExpr_sound` — **proved**.
* `parse_print` (print then parse round-trips) = `mixfix_ok'` — rides on the one open
  `parseExpr_exact`, exactly as the `CBiparser` `ibiparser` does. No *new* sorry is introduced here.
-/

namespace LambdaLab.IsoParser

open LambdaLab.CBiparser LambdaLab.CBiparser.Mixfix

variable {G : Grammar}

/-- **The mixfix parser as an `IsoParser`.** Trivial annotation; reuses `parseCB`/`flatten`. -/
def mixfix (hU : Unambiguous G) (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser (Token G.isSep) (anyTok (G := G)) (follow e) (Expr G e l) (fun _ => PUnit) where
  parse input := (parseCB e l input).map (fun z => (⟨z.1, PUnit.unit⟩, z.2))
  print t _ := t.flatten
  firstOk t rest h := by simp [anyTok] at h
  parse_print t a rest hr := by
    obtain ⟨⟩ := a
    have h := mixfix_ok' hU e l t rest hr
    simp only [biparser, CBiparser.run] at h
    rcases hpc : parseCB e l (t.flatten ++ rest) with _ | ⟨t0, r0⟩
    · rw [hpc] at h; simp at h
    · rw [hpc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hr0⟩ := h
      simp [hpc, hr0]
  print_parse input tea r h := by
    rcases hpc : parseCB e l input with _ | ⟨t0, r0⟩
    · rw [hpc] at h; simp at h
    · rw [hpc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨htea, rfl⟩ := h
      subst htea
      rw [parseCB] at hpc
      rcases hpe : parseExpr e l input with _ | ⟨t0', s0⟩
      · rw [hpe] at hpc; simp at hpc
      · rw [hpe] at hpc
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpc
        obtain ⟨rfl, rfl⟩ := hpc
        exact parseExpr_sound e l input t0' s0 hpe

end LambdaLab.IsoParser
