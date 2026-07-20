import LambdaLab.IsoParser.Basic
import LambdaLab.CBiparser.Mixfix.Complete

/-!
# The mixfix parser, packaged as an `IsoParser`

The whole mixfix development (grammar, `Expr`/`flatten`, the parse algorithm, soundness,
unambiguity) depends only on `Token`, so it is **reused**, not cloned: `mixfix` packages
`parseCB` + `Expr.flatten` as an `IsoParser`, **aligned** (source = value = the tree).

* FIRST is `⊤` (vacuous `firstOk`); FOLLOW is the grammar's computed `follow e` (as the coerced
  proposition).
* The law `ok` = `mixfix_ok'` — conditional on `Unambiguous G`, and it rides on the one open
  `parseExpr_exact`. No *new* sorry is introduced here.
* The exactness direction (`parseExpr_sound` — whatever the parser consumed, `flatten` reproduces)
  is **proved** but has no field in the split model; it remains available standalone.
-/

namespace LambdaLab.IsoParser

open LambdaLab.CBiparser LambdaLab.CBiparser.Mixfix

variable {G : Grammar}

/-- **The mixfix parser as an `IsoParser`.** Aligned; `print` is `flatten`. -/
def mixfix (hU : Unambiguous G) (e : G.Ent) (l : Level (G.entry e)) :
    IsoParser (Token G.isSep) (fun _ => True) (fun t => follow e t = true)
      (Expr G e l) (Expr G e l) where
  parse := parseCB e l
  print t := (t, t.flatten)
  firstOk c rest hc := absurd trivial hc
  ok t rest hr := by
    show (parseCB e l (t.flatten ++ rest)).map (fun z => (z.1, z.2.val)) = some (t, rest)
    have h := mixfix_ok' hU e l t rest hr
    simp only [biparser, CBiparser.run] at h
    rcases hpc : parseCB e l (t.flatten ++ rest) with _ | ⟨t0, r0⟩
    · rw [hpc] at h; simp at h
    · rw [hpc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hr0⟩ := h
      simp [hr0]

end LambdaLab.IsoParser
