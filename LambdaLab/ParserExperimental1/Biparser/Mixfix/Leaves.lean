import LambdaLab.ParserExperimental1.Biparser.Mixfix.Basic
import LambdaLab.ParserExperimental1.Biparser.Example

/-!
# Combinator leaves for the mixfix grammar

Every token/gap the grammar uses is a leaf biparser, so its round-trip is discharged by
its own `parse_complete` (composed by `seq`). Operator **names are multi-character
literals** (`litBip`), variables are single characters (`tok`), and every gap is a
**configurable separator run** `sepRun` (≥1 chars of `G.isSep`, the analogue of the
hard-coded `spaces1`). Each token is pre-composed with its adjacent gap via `seq`
(`lpGap = seq lparen (sepRun G)`, …) so that in the parser each recursive call sits one
`flatMap` deep.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-! ### A multi-character literal, and a configurable separator run. -/

/-- Match a fixed **nonempty** string `s`: renders `s`, parses it as a prefix (`take`/`drop`
at `s.length`). Policy `Unit`, value `Unit`. -/
def litBip (s : List Char) (hne : s ≠ []) : Biparser Char Unit Unit where
  render _ _ := s
  parse input :=
    if h : (input.take s.length == s) = true then
      [((), ⟨input.drop s.length, input.take s.length,
        by rw [eq_of_beq h]; exact hne, List.take_append_drop s.length input⟩)]
    else []
  parse_complete := by
    intro _ _ rest
    have htk : (s ++ rest).take s.length = s := List.take_left
    have hdr : (s ++ rest).drop s.length = rest := List.drop_left
    have hb : ((s ++ rest).take s.length == s) = true := by rw [htk]; exact beq_self_eq_true s
    refine ⟨⟨(s ++ rest).drop s.length, (s ++ rest).take s.length, ?_,
      List.take_append_drop _ _⟩, hdr, ?_⟩
    · rw [htk]; exact hne
    · show ((), _) ∈ (if h : ((s ++ rest).take s.length == s) = true then [((), _)] else [])
      rw [dif_pos hb]; exact List.mem_cons_self

/-- One `G.isSep` character. -/
def sepTok (G : Grammar) : Biparser Char Unit {c : Char // G.isSep c = true} :=
  tok (fun c => G.isSep c)

theorem sep_fm_val {p : Char → Bool} (l : List {c : Char // p c = true}) :
    l.flatMap (fun x => [x.val]) = l.map (·.val) := by
  induction l with | nil => rfl | cons a t ih => simp [List.flatMap_cons, ih]

theorem someRender_seps (G : Grammar) (n : Nat) :
    someRender (sepTok G) (G.sepWitness, List.replicate n G.sepWitness) ()
      = List.replicate (n + 1) G.sepWitness.val := by
  show ((G.sepWitness :: List.replicate n G.sepWitness).flatMap (fun x => [x.val]))
    = List.replicate (n + 1) G.sepWitness.val
  rw [sep_fm_val]; simp [List.map_replicate, List.replicate_succ]

/-- A **separator run**: one or more `G.isSep` characters; policy `Nat` is the extra count
(`render` emits `n+1` copies of the canonical `sepWitness`). The configurable analogue of
`spaces1`. -/
def sepRun (G : Grammar) : Biparser Char Nat Unit where
  render _ n := List.replicate (n + 1) G.sepWitness.val
  parse input := (someParse (sepTok G) input).map (fun r => ((), r.2))
  parse_complete := by
    intro _ n rest
    obtain ⟨s, hs, hmem⟩ := («some» (sepTok G)).parse_complete
      (G.sepWitness, List.replicate n G.sepWitness) () rest
    have hin : someRender (sepTok G) (G.sepWitness, List.replicate n G.sepWitness) () ++ rest
        = List.replicate (n + 1) G.sepWitness.val ++ rest := by rw [someRender_seps G n]
    exact ⟨s.cast hin, by simp [hs],
      List.mem_map.mpr ⟨_, mem_cast_gen (someParse (sepTok G)) hin hmem, rfl⟩⟩

/-! ### The grammar's tokens. -/

def varTok (G : Grammar) : Biparser Char Unit {c : Char // G.isVar c = true} :=
  tok (fun c => G.isVar c)
def lparen : Biparser Char Unit {c : Char // (c == '(') = true} := tok (· == '(')
def rparen : Biparser Char Unit {c : Char // (c == ')') = true} := tok (· == ')')
/-- The operator at precedence `k` as a multi-character literal. -/
def opTok (G : Grammar) (k : Nat) (hk : k < G.ops.length) : Biparser Char Unit Unit :=
  litBip (G.opName k hk) (G.opName_ne k hk)

/-- `"(" ++ gap`. -/
def lpGap (G : Grammar) := seq lparen (sepRun G)
/-- `gap ++ ")"`. -/
def gapRp (G : Grammar) := seq (sepRun G) rparen
/-- `gap ++ opₖ ++ gap` (an infix operator with its surrounding gaps). -/
def gapOpGap (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq (sepRun G) (seq (opTok G k hk) (sepRun G))
/-- `opₖ ++ gap` (a prefix operator with its trailing gap). -/
def opGap (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq (opTok G k hk) (sepRun G)
/-- `gap ++ opₖ` (a postfix operator with its leading gap). -/
def gapOp (G : Grammar) (k : Nat) (hk : k < G.ops.length) :=
  seq (sepRun G) (opTok G k hk)

/-- The bracket / operator token values used by `render`. -/
def lpVal : {c : Char // (c == '(') = true} := ⟨'(', by decide⟩
def rpVal : {c : Char // (c == ')') = true} := ⟨')', by decide⟩
/-- The operator literal's value is trivial (`Unit`) — the name is fixed by `k`. -/
def opVal (G : Grammar) (k : Nat) (_hk : k < G.ops.length) : Unit := ()

end LambdaLab.ParserExperimental1.Mixfix
