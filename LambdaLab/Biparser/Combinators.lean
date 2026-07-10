import LambdaLab.Biparser.Basic

/-!
# Biparser combinators (deterministic, monadic)

Leaves and combinators for `Biparser` (core types + law in `Basic.lean`).
Everything is polymorphic in the alphabet `α`.

Because the leftover is a plain `List α`, `pure` is definable and `Biparser α w`
is a **monad** — `do`, `<$>`, `<*>` all work, and a terminal `pure` (which the old
`RightSublist` leftover forbade) is legal. The two preservation lemmas
(`RoundTrips_pure`, `RoundTrips_bind`) are proved once; `LawfulBiparser` is then a
proof-carrying monad, so any grammar written with `do` is round-trip-correct by
construction — its `.ok` field is the proof, assembled by `bind`.

Leaves: `tok` (fixed literal), `anyTok` (any element), `sat p` (any element
satisfying `p`, source the subtype `{a // p a}` — the variable-token leaf).
`comap` reshapes the source (it is not a monad operation).
-/

namespace LambdaLab.Biparser

/-! ## The monad -/

instance {α w : Type} : Monad (Biparser α w) where
  pure a    := ⟨fun s => some (a, s), fun _ => (a, [])⟩
  bind bw f := ⟨fun s => (bw.parse s).bind fun r => (f r.1).parse r.2,
                fun w => let (v, s) := bw.print w
                         let (t, s') := (f v).print w
                         (t, s ++ s')⟩

/-- How `parse`/`print` act after `pure`/`bind` — all `rfl` (structure eta), so the
round-trip proofs below are straight-line rewriting. -/
theorem parse_bind {α w a b : Type} (bw : Biparser α w a) (f : a → Biparser α w b) (s0 : List α) :
    (bw >>= f).parse s0 = (bw.parse s0).bind fun r => (f r.1).parse r.2 := rfl

theorem print_bind_fst {α w a b : Type} (bw : Biparser α w a) (f : a → Biparser α w b) (src : w) :
    ((bw >>= f).print src).1 = ((f (bw.print src).1).print src).1 := rfl

theorem print_bind_snd {α w a b : Type} (bw : Biparser α w a) (f : a → Biparser α w b) (src : w) :
    ((bw >>= f).print src).2
      = (bw.print src).2 ++ ((f (bw.print src).1).print src).2 := rfl

/-! ## Preservation lemmas -/

/-- `pure` round-trips: prints nothing, parse hands the value straight back. -/
theorem RoundTrips_pure {α w v : Type} (a : v) : RoundTrips (pure a : Biparser α w v) := by
  intro src rest; rfl

/-- `bind` preserves round-tripping — the one lemma that does real work, and with a
plain leftover it is two lines (no `cast`/`transport`). -/
theorem RoundTrips_bind {α w a b : Type} (bw : Biparser α w a) (f : a → Biparser α w b)
    (h1 : RoundTrips bw) (h2 : ∀ x, RoundTrips (f x)) : RoundTrips (bw >>= f) := by
  intro src rest
  rw [print_bind_snd, print_bind_fst, parse_bind, List.append_assoc, h1 src]
  exact h2 (bw.print src).1 src rest

/-! ## The proof-carrying monad -/

instance {α w : Type} : Monad (LawfulBiparser α w) where
  pure a    := ⟨pure a, RoundTrips_pure a⟩
  bind x f  := ⟨x.toBiparser >>= fun a => (f a).toBiparser,
                RoundTrips_bind x.toBiparser (fun a => (f a).toBiparser) x.ok (fun a => (f a).ok)⟩

/-! ## Leaves -/

/-- The single-element literal leaf. -/
def tok {α : Type} [DecidableEq α] (c : α) : Biparser α Unit α where
  parse
    | []        => none
    | c' :: rest => if c = c' then some (c, rest) else none
  print _ := (c, [c])

theorem RoundTrips_tok {α : Type} [DecidableEq α] (c : α) : RoundTrips (tok c) := by
  intro _ rest; simp [tok]

/-- Any single element; prints whatever its source carries. -/
def anyTok {α : Type} : Biparser α α α where
  parse
    | []        => none
    | c :: rest => some (c, rest)
  print src := (src, [src])

theorem RoundTrips_anyTok {α : Type} : RoundTrips (anyTok (α := α)) :=
  fun _ _ => rfl

/-- Any element satisfying `p`; source is the subtype `{a // p a = true}`, so `print`
always emits a `p`-element and `parse`'s guard succeeds. The variable-token leaf. -/
def sat {α : Type} (p : α → Bool) : Biparser α {a : α // p a = true} α where
  parse
    | []        => none
    | c :: rest => if p c then some (c, rest) else none
  print src := (src.1, [src.1])

theorem RoundTrips_sat {α : Type} (p : α → Bool) : RoundTrips (sat p) := by
  intro src rest; simp [sat, src.2]

/-! ## Combinators: `map`, `seq`, `comap`

`map`/`seq` are also derivable from the monad (`<$>`/`<*>`); they are kept explicit
for direct use and to state their preservation lemmas (which are now short). -/

def map {α w a b : Type} (f : a → b) (bw : Biparser α w a) : Biparser α w b where
  parse s := (bw.parse s).map fun r => (f r.1, r.2)
  print src := let (v, s) := bw.print src; (f v, s)

theorem RoundTrips_map {α w a b : Type} (f : a → b) (bw : Biparser α w a)
    (h : RoundTrips bw) : RoundTrips (map f bw) := by
  intro src rest
  show ((bw.parse ((bw.print src).2 ++ rest)).map fun r => (f r.1, r.2))
        = some (f (bw.print src).1, rest)
  rw [h src]; rfl

def seq {α w a b : Type} (bw1 : Biparser α w a) (bw2 : Biparser α w b) : Biparser α w (a × b) where
  parse s := (bw1.parse s).bind fun r1 => (bw2.parse r1.2).map fun r2 => ((r1.1, r2.1), r2.2)
  print src :=
    (((bw1.print src).1, (bw2.print src).1), (bw1.print src).2 ++ (bw2.print src).2)

theorem RoundTrips_seq {α w a b : Type} (bw1 : Biparser α w a) (bw2 : Biparser α w b)
    (h1 : RoundTrips bw1) (h2 : RoundTrips bw2) : RoundTrips (seq bw1 bw2) := by
  intro src rest
  show ((bw1.parse ((((bw1.print src).2 ++ (bw2.print src).2)) ++ rest)).bind fun r1 =>
        (bw2.parse r1.2).map fun r2 => ((r1.1, r2.1), r2.2)) = _
  rw [List.append_assoc, h1 src]
  show ((bw2.parse ((bw2.print src).2 ++ rest)).map fun r2 =>
        (((bw1.print src).1, r2.1), r2.2)) = _
  rw [h2 src]; rfl

/-- `comap` reshapes the source contravariantly — lets two `seq`/`do` steps print
different parts of a shared source. Touches only `print`, so its law is immediate. -/
def comap {α w w' v : Type} (g : w' → w) (bp : Biparser α w v) : Biparser α w' v where
  parse := bp.parse
  print src := bp.print (g src)

theorem RoundTrips_comap {α w w' v : Type} (g : w' → w) (bp : Biparser α w v)
    (h : RoundTrips bp) : RoundTrips (comap g bp) := fun src rest => h (g src) rest

/-! ## Proof-carrying leaves / smart constructors -/

def ltok {α : Type} [DecidableEq α] (c : α) : LawfulBiparser α Unit α := ⟨tok c, RoundTrips_tok c⟩

def lanyTok {α : Type} : LawfulBiparser α α α := ⟨anyTok, RoundTrips_anyTok⟩

def lsat {α : Type} (p : α → Bool) : LawfulBiparser α {a : α // p a = true} α :=
  ⟨sat p, RoundTrips_sat p⟩

def lcomap {α w w' v : Type} (g : w' → w) (x : LawfulBiparser α w v) : LawfulBiparser α w' v :=
  ⟨comap g x.toBiparser, RoundTrips_comap g x.toBiparser x.ok⟩

/-! ## Demonstration (over `α = Char`)

Grammars are written with `do`, ending in `pure` — the thing the `RightSublist`
leftover forbade. Each comes out proof-carrying for free. -/

/-- A literal sequence, `do` with a terminal `pure`. -/
def abc : LawfulBiparser Char Unit (Char × Char × Char) := do
  let a ← ltok 'a'
  let b ← ltok 'b'
  let c ← ltok 'c'
  pure (a, b, c)

/-- Structured data via `comap` + `do`: nobody writes a printer — `print (a,b)`
falls out as `((a,b), [a,b])`, and the round-trip proof threads through `bind`. -/
def pair : LawfulBiparser Char (Char × Char) (Char × Char) := do
  let a ← lcomap Prod.fst lanyTok
  let b ← lcomap Prod.snd lanyTok
  pure (a, b)

/-- The variable-token leaf: any digit. -/
def digit : LawfulBiparser Char {c : Char // Char.isDigit c = true} Char := lsat Char.isDigit

-- All proof-carrying, for free:
#check (abc.ok   : RoundTrips abc.toBiparser)
#check (pair.ok  : RoundTrips pair.toBiparser)
#check (digit.ok : RoundTrips digit.toBiparser)

#eval abc.parse   "abcd".toList   -- some (('a','b','c'), ['d'])
#eval abc.print   ()              -- (('a','b','c'), ['a','b','c'])
#eval pair.parse  "xyz".toList    -- some (('x','y'), ['z'])
#eval pair.print  ('x', 'y')      -- (('x','y'), ['x','y'])
#eval digit.parse "7a".toList     -- some ('7', ['a'])

end LambdaLab.Biparser
