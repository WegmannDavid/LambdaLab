import LambdaLab.CBiparser.RoundTrip

/-!
# `IBip` — FIRST/FOLLOW in the type; the law rides along

`RoundTrips` is a law *beside* the biparser, with `F` threaded through every lemma — the same
anti-pattern that a progress predicate would be. So bundle it: an `IBip` **carries its own
round-trip proof**, and FIRST/FOLLOW are **type indices**.

Indexing (rather than making them fields) is what makes `iBind` possible. A continuation's
type `k : v → IBip f₂ fo₂ w v'` *asserts* that every `k a` has the same FIRST and FOLLOW — the
uniformity condition becomes a typing rule instead of a proof obligation. What it rules out is
a grammar whose *shape* depends on what it parsed: exactly the condition LL parsing has always
required, now enforced by the typechecker.

The payoff is `IBip.roundtrip`: **every** `IBip` round-trips terminally, with no side-condition
and no per-grammar proof. Build the grammar from the combinators and the law is already proved.
The only obligations left are the **seams**, which are the genuine content — the lexical facts
that make the grammar unambiguous.
-/

namespace LambdaLab.CBiparser

variable {α : Type} {fst fol f₁ fo₁ f₂ fo₂ : α → Bool} {w v v' : Type}

/-- A biparser carrying its round-trip law, indexed by its FIRST and FOLLOW sets.

It **extends** `CBiparser`: an `IBip` *is* a biparser, with extra structure — so `p.parse`,
`p.print` and `p.run` work directly, with no `.bp` indirection. -/
structure IBip {α : Type} (fst fol : α → Bool) (w v : Type) extends CBiparser α w v where
  /-- FIRST is sound: outside it, the parse fails. -/
  firstOk : ∀ (a : α) (rest : List α), fst a = false → toCBiparser.run (a :: rest) = none
  /-- The law, bundled. -/
  ok      : RoundTrips toCBiparser (HeadIn fol)

/-- Nothing outside FIRST parses — *including* empty input, by `run_nil`. -/
theorem IBip.noParse (p : IBip fst fol w v) (rest : List α)
    (h : ∀ a, rest.head? = some a → fst a = false) : p.run rest = none := by
  cases rest with
  | nil => exact run_nil _
  | cons a as => exact p.firstOk a as (h a rfl)

/-- **The payoff.** Print any source, parse it back, recover the value with nothing left over —
no side-conditions, no per-grammar proof. `HeadIn f []` is vacuous, so end-of-input discharges
the FOLLOW by itself. -/
theorem IBip.roundtrip (p : IBip fst fol w v) (s : w) :
    p.run (p.print s).2 = some ((p.print s).1, []) := by
  have h := p.ok s [] (HeadIn_nil _)
  simpa using h

/-- A printed output always starts with a symbol in FIRST — *derived* from `ok` + `firstOk`,
not assumed. This is what lets `iBind` discharge its internal seam. -/
theorem IBip.head_first (q : IBip fst fol w v) (s : w) (rest : List α)
    (hrest : HeadIn fol rest) (a : α)
    (ha : ((q.print s).2 ++ rest).head? = some a) : fst a = true := by
  cases hfa : fst a with
  | true => rfl
  | false =>
      exfalso
      have hnone : q.run ((q.print s).2 ++ rest) = none := by
        apply IBip.noParse
        intro a' ha'
        rw [ha] at ha'
        exact (Option.some.inj ha') ▸ hfa
      rw [q.ok s rest hrest] at hnone
      exact absurd hnone (by simp)

/-! ## Leaves -/

/-- A **fixed token**. Prints constant content, so its source is polymorphic; consumes exactly
one symbol, so it is self-delimiting (`FOLLOW = ⊤`). -/
def iTok [DecidableEq α] (t : α) : IBip (fun a => decide (a = t)) (fun _ => true) w α where
  parse := fun input =>
    match input with
    | [] => none
    | hd :: tl => if hd = t then some (hd, ⟨tl, by simp⟩) else none
  print := fun _ => (t, [t])
  firstOk := by
    intro a rest h
    have hne : ¬ (a = t) := by simpa using h
    simp [CBiparser.run, hne]
  ok := by
    intro _ rest _
    simp [CBiparser.run]

/-- **Any token satisfying `f`** — the general "lexical class" leaf (identifiers, literals, …).

The source is `{a // f a = true}`, not `α`: a source outside the class would print a symbol the
parser rejects, so it must be **unrepresentable**. Same medicine as everywhere else — put the
validity invariant in the source type and no proof ever carries a well-formedness hypothesis. -/
def iSat (f : α → Bool) :
    IBip f (fun _ => true) { a : α // f a = true } { a : α // f a = true } where
  parse := fun input =>
    match input with
    | [] => none
    | hd :: tl => if h : f hd then some (⟨hd, h⟩, ⟨tl, by simp⟩) else none
  print := fun a => (a, [a.val])
  firstOk := by
    intro a rest h
    simp [CBiparser.run, h]
  ok := by
    intro a rest _
    simp [CBiparser.run, a.property]

/-- Adapt the **source**: `iComap f p` prints from `w'` by first projecting to `w`. FIRST and
FOLLOW are unchanged (they are parse-side data, and parse ignores the source).

This is how a node with several sub-parsers works: the node's source is a *product*, and each
sub-parser `iComap`s the projection it needs. -/
def iComap (f : w' → w) (p : IBip fst fol w v) : IBip fst fol w' v where
  toCBiparser := comap f p.toCBiparser
  firstOk := p.firstOk
  ok := RoundTrips_comap f p.toCBiparser _ p.ok

/-- **Weaken the FOLLOW.** `RoundTrips` is antitone in FOLLOW — a *smaller* FOLLOW admits fewer
continuations, so it is a weaker (still true) claim. This is what lets a parser with a broad
natural FOLLOW be plugged into an interface that pins FOLLOW to specific key tokens: state your
real FOLLOW, then weaken at the boundary. -/
def IBip.weakenFollow {fol' : α → Bool} (h : ∀ a, fol' a = true → fol a = true)
    (p : IBip fst fol w v) : IBip fst fol' w v :=
  { p with ok := RoundTrips_mono (fun _ hr a ha => h a (hr a ha)) p.ok }

/-- **Enlarge the FIRST.** `firstOk` is a purely *negative* claim — "outside FIRST, I fail" —
so a *larger* FIRST is a **weaker** claim, and always sound. (Enlarging all the way to `⊤` makes
`firstOk` vacuous, which is exactly right: it then promises nothing.)

Dual of `weakenFollow`. Together they are the plug-in boundary: state your parser's real FIRST
and FOLLOW, then `enlargeFirst` / `weakenFollow` to whatever the interface demands. -/
def IBip.enlargeFirst {fst' : α → Bool} (h : ∀ a, fst' a = false → fst a = false)
    (p : IBip fst fol w v) : IBip fst' fol w v :=
  { p with firstOk := fun a rest hf => p.firstOk a rest (h a hf) }

/-! ## Combinators — the law is rebuilt, never re-proved -/

def iMap (f : v → v') (p : IBip fst fol w v) : IBip fst fol w v' where
  toCBiparser := f <$> p.toCBiparser
  firstOk := by intro a rest h; simp [map_run, p.firstOk a rest h]
  ok := RoundTrips_map f p.toCBiparser _ p.ok

/-- **Monadic bind** — possible because `k`'s *type* pins its FIRST/FOLLOW independently of the
parsed value. The seam is its one and only obligation. -/
def iBind (p : IBip f₁ fo₁ w v) (k : v → IBip f₂ fo₂ w v')
    (hseam : ∀ a, f₂ a = true → fo₁ a = true) : IBip f₁ fo₂ w v' where
  toCBiparser := p.toCBiparser >>= fun a => (k a).toCBiparser
  firstOk := by intro a rest h; simp [bind_run, p.firstOk a rest h]
  ok := by
    refine RoundTrips_bind p.toCBiparser _ (HeadIn fo₂) (HeadIn fo₁) p.ok (fun a => (k a).ok) ?_
    intro s rest hrest a ha
    exact hseam a ((k (p.print s).1).head_first s rest hrest a ha)

/-- One-or-more. FOLLOW *computes*: the continuation may not start another element. `hrep`
("an element's own output may follow an element") is `FIRST ⊆ FOLLOW`. -/
def iMany1 (p : IBip fst fol w v) (hrep : ∀ a, fst a = true → fol a = true) :
    IBip fst (fun a => fol a && !fst a) (NEList w) (List v) where
  toCBiparser := many1NE p.toCBiparser
  firstOk := by intro a rest h; rw [many1NE_run_eq, p.firstOk a rest h]
  ok := by
    have hclosed : ∀ (s : w) (r : List α),
        HeadIn fol r → HeadIn fol ((p.print s).2 ++ r) := by
      intro s r hr a ha
      cases hout : (p.print s).2 with
      | nil => rw [hout] at ha; simp at ha; exact hr a ha
      | cons a0 as =>
          rw [hout] at ha; simp at ha
          subst ha
          exact hrep a0 (p.head_first s [] (HeadIn_nil _) a0 (by rw [hout]; rfl))
    refine RoundTrips_mono ?_ (RoundTrips_many1NE p.toCBiparser (HeadIn fol) p.ok hclosed)
    intro rest hr
    refine ⟨fun a ha => ?_, ?_⟩
    · have := hr a ha; simpa using (Bool.and_eq_true .. |>.mp this).1
    · apply IBip.noParse
      intro a ha
      have := hr a ha
      simpa using (Bool.and_eq_true .. |>.mp this).2

/-! ## `do`-notation

`iBind` is an *indexed* monad — the indices change across a bind — so Lean's `Bind`/`do`
cannot apply. A macro can. Each seam is threaded as `(by seam)`; `seam` tries the common
shapes and will pick up any facts you bring into scope with `have` before the block. -/

/-- Discharge a seam: `∀ a, FIRST₂ a → FOLLOW₁ a`. These are the lexical facts that make the
grammar unambiguous. Bring the needed ones into scope (`have h := …`) before a `gdo` block. -/
macro "seam" : tactic => `(tactic| (
  intro a ha
  first
    | rfl
    | assumption
    | simp_all
    | decide))

syntax "gdo " ("let " ident " ← " term ";"?)+ "return " term : term

macro_rules
  | `(gdo $[let $xs ← $ps $[;]?]* return $e) => do
      let n := xs.size
      let mut acc ← `(iMap (fun $(xs[n-1]!) => $e) $(ps[n-1]!))
      for i in [0:n-1] do
        let j := n - 2 - i
        acc ← `(iBind $(ps[j]!) (fun $(xs[j]!) => $acc) (by seam))
      return acc

end LambdaLab.CBiparser
