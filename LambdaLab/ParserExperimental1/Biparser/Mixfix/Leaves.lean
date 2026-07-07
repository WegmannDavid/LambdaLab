import LambdaLab.ParserExperimental1.Biparser.Mixfix.Basic
import LambdaLab.ParserExperimental1.Biparser.Example

/-!
# Combinator leaves for the mixfix grammar

Every token/gap the grammar uses is a leaf biparser, so its round-trip is discharged by
its own `parse_complete` (composed by `seq`). Operator **names are multi-character
literals** (`litBip`), variables are multi-character words (`varWord`), and every gap is a
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

/-- One non-separator character. -/
def nonSepTok (G : Grammar) : Biparser Char Unit {c : Char // (!G.isSep c) = true} :=
  tok (fun c => !G.isSep c)

/-- Package a provably-separator-free char list as a list of non-separator tokens. -/
def toNonSep (G : Grammar) : (l : List Char) → (∀ c ∈ l, G.isSep c = false) →
    List {c : Char // (!G.isSep c) = true}
  | [],      _ => []
  | c :: cs, h => ⟨c, by simp [h c List.mem_cons_self]⟩ ::
      toNonSep G cs (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem toNonSep_map (G : Grammar) (l : List Char) (h : ∀ c ∈ l, G.isSep c = false) :
    (toNonSep G l h).map (·.val) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [toNonSep, ih]

/-- The chars of a non-separator run are all non-separators. -/
theorem run_sepFree (G : Grammar) (b : {c : Char // (!G.isSep c) = true})
    (bs : List {c : Char // (!G.isSep c) = true}) :
    ∀ c ∈ (b.val :: bs.map (·.val)), G.isSep c = false := by
  intro c hc
  simp only [List.mem_cons, List.mem_map] at hc
  rcases hc with rfl | ⟨x, _, rfl⟩
  · simpa using b.property
  · simpa using x.property

/-- The `filterMap` step turning a non-separator run into a variable token when `isVar`
accepts its chars. -/
def varMk (G : Grammar) {input : List Char}
    (r : ({c : Char // (!G.isSep c) = true} × List {c : Char // (!G.isSep c) = true}) ×
      RightSublist input) : Option (VarTok G × RightSublist input) :=
  if h : G.isVar (r.1.1.val :: r.1.2.map (·.val)) = true then
    Option.some ((⟨r.1.1.val :: r.1.2.map (·.val), List.cons_ne_nil _ _, run_sepFree G r.1.1 r.1.2, h⟩ : VarTok G), r.2)
  else Option.none

/-- A **variable word**: a nonempty separator-free run that `isVar` accepts. Renders its
chars; parses **every** nonempty separator-free `isVar` prefix (the all-parses model — the
intended variable is always among them, which is all `parse_complete` needs). -/
def varWord (G : Grammar) : Biparser Char Unit (VarTok G) where
  render v _ := v.chars
  parse input := (someParse (nonSepTok G) input).filterMap (varMk G)
  parse_complete := by
    intro v _ rest
    obtain ⟨c0, cs', hcons⟩ := List.exists_cons_of_ne_nil v.hne
    have hc0 : (!G.isSep c0) = true := by
      have := v.hsf c0 (by rw [hcons]; exact List.mem_cons_self); simp [this]
    have hcs' : ∀ c ∈ cs', G.isSep c = false := fun c hc =>
      v.hsf c (by rw [hcons]; exact List.mem_cons_of_mem _ hc)
    obtain ⟨s0, hs0, hmem0⟩ := («some» (nonSepTok G)).parse_complete
      (⟨c0, hc0⟩, toNonSep G cs' hcs') () rest
    have hch : (⟨c0, hc0⟩ : {c : Char // (!G.isSep c) = true}).val ::
        (toNonSep G cs' hcs').map (·.val) = v.chars := by
      show c0 :: (toNonSep G cs' hcs').map (·.val) = v.chars
      rw [toNonSep_map, hcons]
    have hren : («some» (nonSepTok G)).render (⟨c0, hc0⟩, toNonSep G cs' hcs') () = v.chars := by
      show ((⟨c0, hc0⟩ : {c : Char // (!G.isSep c) = true}) :: toNonSep G cs' hcs').flatMap
          (fun x => [x.val]) = v.chars
      rw [sep_fm_val]; exact hch
    have hin : («some» (nonSepTok G)).render (⟨c0, hc0⟩, toNonSep G cs' hcs') () ++ rest
        = v.chars ++ rest := by rw [hren]
    refine ⟨s0.cast hin, by simp [hs0], ?_⟩
    show (v, s0.cast hin) ∈ (someParse (nonSepTok G) (v.chars ++ rest)).filterMap (varMk G)
    rw [List.mem_filterMap]
    refine ⟨((⟨c0, hc0⟩, toNonSep G cs' hcs'), s0.cast hin), ?_, ?_⟩
    · exact mem_cast_gen (someParse (nonSepTok G)) hin hmem0
    · show varMk G ((⟨c0, hc0⟩, toNonSep G cs' hcs'), s0.cast hin) = Option.some (v, s0.cast hin)
      unfold varMk
      simp only [hch, dif_pos v.hv]

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
