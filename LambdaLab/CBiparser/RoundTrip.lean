import LambdaLab.CBiparser.Basic

/-!
# The round-trip law

Weak backward round-tripping, parameterised by a **FOLLOW** condition `F`: printing any
source, appending any `F`-admissible continuation, and re-parsing recovers the printed value
and hands the continuation back untouched.

`F` is a parameter, not a constant, because greedy combinators (`many1NE`) genuinely depend on
what follows them — that dependence *is* the statement "this grammar is unambiguous", and it
cannot be deleted. What *can* be avoided is threading it by hand: the law is stated against
the printer's *own output value*, which makes `RoundTrips_bind` a rewrite chain, so each
combinator's law is proved **once** and every biparser built from it inherits its law.
-/

namespace LambdaLab.CBiparser

variable {α : Type} {w v v' : Type}

/-- The FOLLOW condition, as a class of admissible *next symbols*. Vacuously true at `[]` —
which is exactly why end-of-input needs no proof. -/
def HeadIn (f : α → Bool) (rest : List α) : Prop :=
  ∀ a, rest.head? = some a → f a = true

@[simp] theorem HeadIn_nil (f : α → Bool) : HeadIn f ([] : List α) := by
  intro a ha; simp at ha

/-- `p` round-trips w.r.t. `F`. -/
def RoundTrips (p : CBiparser α w v) (F : List α → Prop) : Prop :=
  ∀ (s : w) (rest : List α), F rest →
    p.run ((p.print s).2 ++ rest) = some ((p.print s).1, rest)

/-- Antitone in `F`: a *stronger* FOLLOW admits fewer continuations. -/
theorem RoundTrips_mono {p : CBiparser α w v} {F F' : List α → Prop}
    (h : ∀ rest, F' rest → F rest) (hp : RoundTrips p F) : RoundTrips p F' :=
  fun s rest hF' => hp s rest (h rest hF')

/-- `comap` preserves the law: parse is untouched, and printing from `w'` just prints from
`f w'`. This is what lets one node's sub-parsers pull *different* slices out of a shared
source — the multi-operand case. -/
theorem RoundTrips_comap (f : w' → w) (p : CBiparser α w v) (F : List α → Prop)
    (hp : RoundTrips p F) : RoundTrips (comap f p) F :=
  fun s rest hF => hp (f s) rest hF

theorem RoundTrips_map (f : v → v') (p : CBiparser α w v) (F : List α → Prop)
    (hp : RoundTrips p F) : RoundTrips (f <$> p) F := by
  intro s rest hF
  simp [map_print, map_run, hp s rest hF]

/-- **The compositional heart.** The seam — `k`'s printed output must be an admissible FOLLOW
for `p` — is discharged here, once. -/
theorem RoundTrips_bind (p : CBiparser α w v) (k : v → CBiparser α w v')
    (F Fp : List α → Prop)
    (hp : RoundTrips p Fp)
    (hk : ∀ a, RoundTrips (k a) F)
    (hseam : ∀ (s : w) (rest : List α), F rest →
        Fp (((k (p.print s).1).print s).2 ++ rest)) :
    RoundTrips (p >>= k) F := by
  intro s rest hF
  have h1 := hp s (((k (p.print s).1).print s).2 ++ rest) (hseam s rest hF)
  have h2 := hk (p.print s).1 s rest hF
  rw [bind_print, bind_run, List.append_assoc, h1]
  exact h2

/-- `F` survives having a whole *run* of printed elements prepended. -/
theorem F_closed_run (p : CBiparser α w v) (F : List α → Prop)
    (hclosed : ∀ (s : w) (r : List α), F r → F ((p.print s).2 ++ r)) :
    ∀ (vs : List w) (rest : List α), F rest → F ((many1Print p vs).2 ++ rest) := by
  intro vs
  induction vs with
  | nil => intro rest hF; rw [many1Print_nil]; simpa using hF
  | cons x xs ih =>
      intro rest hF
      have h2 := hclosed x _ (ih rest hF)
      rwa [many1Print_cons_snd, List.append_assoc]

/-- **The greedy seam.** `many1NE p` round-trips at a FOLLOW that (a) is admissible for the
element and (b) forbids the continuation from starting *another* element. -/
theorem RoundTrips_many1NE (p : CBiparser α w v) (F : List α → Prop)
    (hp : RoundTrips p F)
    (hclosed : ∀ (s : w) (r : List α), F r → F ((p.print s).2 ++ r)) :
    RoundTrips (many1NE p) (fun rest => F rest ∧ p.run rest = none) := by
  rintro ⟨u, us⟩ rest ⟨hF, hnone⟩
  have hnone' : (many1NE p).run rest = none := by rw [many1NE_run_eq, hnone]
  show (many1NE p).run ((many1Print p (u :: us)).2 ++ rest)
      = some ((many1Print p (u :: us)).1, rest)
  -- each `rw` fires once by design: `many1NE_run_eq` is a recursion equation (as a `simp`
  -- lemma it loops), and the `many1Print` equations must not decompose the folded term `ih`
  -- is about.
  induction us generalizing u with
  | nil =>
      rw [many1Print_cons_snd, many1Print_cons_fst, many1Print_nil]
      simp only [List.append_nil]
      rw [many1NE_run_eq, hp u rest hF]
      dsimp only
      rw [hnone']
  | cons u' us' ih =>
      rw [many1Print_cons_snd, many1Print_cons_fst, List.append_assoc, many1NE_run_eq,
          hp u _ (F_closed_run p F hclosed (u' :: us') rest hF)]
      dsimp only
      rw [ih u']

end LambdaLab.CBiparser
