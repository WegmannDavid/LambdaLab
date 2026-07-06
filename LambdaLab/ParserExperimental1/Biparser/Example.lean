import LambdaLab.ParserExperimental1.Biparser.Combinators

/-!
# Example: space-separated unary naturals, variable gaps + optional edges (weak target)

Parses a **nonempty** sequence of unary numbers (`a`=0, `aa`=1, …) where numbers are
separated by **one or more** spaces and the whole input may have leading/trailing
spaces, e.g. `"  a   aaa  aa "` ↦ `(0, [2, 1])`. Only `parse_complete` is required, so
this need not (and cannot) satisfy `render_complete` — the parser accepts variable and
optional whitespace that no single rendering reproduces. `NatsPolicy := Nat` chooses the
(uniform) gap size that `render` emits; parse still accepts any ≥1-space gaps and
optional edges.
-/

namespace LambdaLab.ParserExperimental1

abbrev Nats := Nat × List Nat
/-- The formatting choice: the gap **after** each number is a function of that number
(`render` emits `f n + 1` spaces after a number valued `n`). -/
abbrev NatsPolicy : Type := Nat → Nat

def aTok  : Biparser Char Unit { c : Char // (c == 'a') = true } := tok (· == 'a')
def spTok : Biparser Char Unit { c : Char // (c == ' ') = true } := tok (· == ' ')

/-! ### `spaces1`: a run of ≥1 spaces, policy = extra count -/

theorem fm_val (l : List { c : Char // (c == ' ') = true }) :
    l.flatMap (fun x => [x.val]) = l.map (·.val) := by
  induction l with | nil => rfl | cons a t ih => simp [List.flatMap_cons, ih]

theorem someRender_spaces (n : Nat) :
    someRender spTok (⟨' ', by decide⟩, List.replicate n ⟨' ', by decide⟩) ()
      = List.replicate (n + 1) ' ' := by
  show ((⟨' ', by decide⟩ : { c : Char // (c == ' ') = true }) :: List.replicate n ⟨' ', by decide⟩).flatMap
        (fun x => [x.val]) = List.replicate (n + 1) ' '
  rw [fm_val]; simp [List.map_replicate, List.replicate_succ]

def spaces1 : Biparser Char Nat Unit where
  render _ n := List.replicate (n + 1) ' '
  parse input := (someParse spTok input).map (fun r => ((), r.2))
  parse_complete := by
    intro _ n rest
    obtain ⟨s, hs, hmem⟩ := («some» spTok).parse_complete
      (⟨' ', by decide⟩, List.replicate n ⟨' ', by decide⟩) () rest
    have hin : someRender spTok (⟨' ', by decide⟩, List.replicate n ⟨' ', by decide⟩) () ++ rest
        = List.replicate (n + 1) ' ' ++ rest := by rw [someRender_spaces n]
    exact ⟨s.cast hin, by simp [hs],
      List.mem_map.mpr ⟨_, mem_cast_gen (someParse spTok) hin hmem, rfl⟩⟩

/-! ### The pipeline -/

/-- One unary number → `Nat` (run's tail length). -/
def number : Biparser Char Unit Nat :=
  map («some» aTok) (fun v => v.2.length)
    (fun n => (⟨'a', by decide⟩, List.replicate n ⟨'a', by decide⟩)) (fun n => by simp)

/-- A number **with its trailing gap**: renders the number, then `f n + 1` spaces where
`n` is the number's own value — so the gap "behind" a nat depends on the nat. Parse reuses
`seq number spaces1` (the render is defeq to it at policy `((), f n)`), forgetting the
space. -/
def numberWithGap : Biparser Char (Nat → Nat) Nat where
  render n f := number.render n () ++ List.replicate (f n + 1) ' '
  parse input := ((seq number spaces1).parse input).map (fun r => (r.1.1, r.2))
  parse_complete := by
    intro n f rest
    obtain ⟨s, hs, hmem⟩ := (seq number spaces1).parse_complete (n, ()) ((), f n) rest
    exact ⟨s, hs, List.mem_map.mpr ⟨((n, ()), s), hmem, rfl⟩⟩

/-- Assemble the full list from `(≥1 with-gap numbers) ++ [final]`, or a lone number. -/
def numbersTo : ((Nat × List Nat) × Nat) ⊕ Nat → Nat × List Nat
  | .inl ((h, t), final) => (h, t ++ [final])
  | .inr n               => (n, [])

/-- Split off the last number (which has no trailing gap). -/
def numbersFro : Nat × List Nat → ((Nat × List Nat) × Nat) ⊕ Nat
  | (n, [])      => .inr n
  | (n, m :: ms) => .inl ((n, (m :: ms).dropLast), (m :: ms).getLast (by simp))

/-- ≥1 numbers: ≥1 `numberWithGap`s (each carrying its trailing gap) then a final bare
number, or a lone number; reshaped to `Nats`. The final number has no trailing gap. -/
def numbers :=
  map (alt (seq («some» numberWithGap) number) number) numbersTo numbersFro (by
    intro c
    obtain ⟨n, l⟩ := c
    cases l with
    | nil => rfl
    | cons m ms => simp [numbersTo, numbersFro, List.dropLast_concat_getLast])

/-- Accept an optional leading space-run (rendered absent: `fro` picks the no-lead
branch). -/
def withLead :=
  map (alt (seq spaces1 numbers) numbers)
    (fun v => match v with | .inl (_, ns) => ns | .inr ns => ns)
    (fun ns => .inr ns)
    (fun _ => rfl)

/-- Accept an optional trailing space-run likewise. -/
def withTrail :=
  map (alt (seq withLead spaces1) withLead)
    (fun v => match v with | .inl (ns, _) => ns | .inr ns => ns)
    (fun ns => .inr ns)
    (fun _ => rfl)

/-- The parser: expose the gap function `f : Nat → Nat` as the policy; the reshaping map
rebuilds the nested `withTrail` policy from `f` (dead leading/trailing-run slots = 0). -/
def parseNats : Biparser Char NatsPolicy Nats :=
  mapPolicy (fun f : NatsPolicy =>
    let nP  : ((NatsPolicy) × Unit) × Unit := ((f, ()), ())
    let wlP : (Nat × (((NatsPolicy) × Unit) × Unit)) × (((NatsPolicy) × Unit) × Unit) := ((0, nP), nP)
    ((wlP, 0), wlP))
    withTrail

#eval (parseNats.parse "  a   aaa  aa ".toList).filter (fun r => r.2.list.isEmpty) |>.map (·.1)
  -- [(0, [2, 1])] — leading/variable-gaps/trailing all accepted
#eval String.ofList (parseNats.render (0, [2, 1]) (fun _ => 0))   -- gaps all 1 space: "a aaa aa"
#eval String.ofList (parseNats.render (0, [2, 1]) (fun n => n))   -- gap after n = n spaces: n=0→1sp, n=2→3sp, n=1→2sp
#eval String.ofList (parseNats.render (0, [2, 1]) (fun n => n + 1)) -- gap after n = n+2 spaces

end LambdaLab.ParserExperimental1
