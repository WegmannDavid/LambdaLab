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
/-- The one real formatting choice: uniform gap size (`render` emits `gap+1` spaces
between numbers). -/
abbrev NatsPolicy : Type := Nat

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

/-- `spaces1` then a number, valued by the number. -/
def gapNumber : Biparser Char (Nat × Unit) Nat :=
  map (seq spaces1 number) (fun v => v.2) (fun n => ((), n)) (fun _ => rfl)

/-- ≥1 numbers: a number, then ≥1 `gap number`s, or a lone number; reshaped to `Nats`. -/
def numbers : Biparser Char ((Unit × (Nat × Unit)) × Unit) Nats :=
  map (alt (seq number («some» gapNumber)) number)
    (fun v => match v with | .inl (n, (m, ms)) => (n, m :: ms) | .inr n => (n, []))
    (fun v => match v with | (n, []) => .inr n | (n, m :: ms) => .inl (n, (m, ms)))
    (fun v => by obtain ⟨n, l⟩ := v; cases l <;> rfl)

/-- Accept an optional leading space-run (rendered absent: `fro` picks the no-lead
branch). -/
def withLead : Biparser Char ((Nat × ((Unit × (Nat × Unit)) × Unit)) × ((Unit × (Nat × Unit)) × Unit)) Nats :=
  map (alt (seq spaces1 numbers) numbers)
    (fun v => match v with | .inl (_, ns) => ns | .inr ns => ns)
    (fun ns => .inr ns)
    (fun _ => rfl)

/-- Accept an optional trailing space-run likewise. -/
def withTrail :
    Biparser Char
      ((((Nat × ((Unit × (Nat × Unit)) × Unit)) × ((Unit × (Nat × Unit)) × Unit)) × Nat) ×
        ((Nat × ((Unit × (Nat × Unit)) × Unit)) × ((Unit × (Nat × Unit)) × Unit))) Nats :=
  map (alt (seq withLead spaces1) withLead)
    (fun v => match v with | .inl (ns, _) => ns | .inr ns => ns)
    (fun ns => .inr ns)
    (fun _ => rfl)

/-- The parser: expose only the uniform gap size as the policy. The reshaping map
rebuilds the whole nested `withTrail` policy from the single `g`, filling every gap slot
(and the dead leading/trailing-run slots) uniformly. -/
def parseNats : Biparser Char NatsPolicy Nats :=
  mapPolicy (fun g : Nat =>
    let nP  : (Unit × (Nat × Unit)) × Unit := (((), (g, ())), ())
    let wlP : (Nat × ((Unit × (Nat × Unit)) × Unit)) × ((Unit × (Nat × Unit)) × Unit) := ((g, nP), nP)
    ((wlP, g), wlP))
    withTrail

#eval (parseNats.parse "  a   aaa  aa ".toList).filter (fun r => r.2.list.isEmpty) |>.map (·.1)
  -- [(0, [2, 1])] — leading/variable-gaps/trailing all accepted
#eval String.ofList (parseNats.render (0, [2, 1]) 0)  -- "a aaa aa"  (gap 0 ⇒ 1 space)
#eval String.ofList (parseNats.render (0, [2, 1]) 2)  -- "a   aaa   aa"  (gap 2 ⇒ 3 spaces)

end LambdaLab.ParserExperimental1
