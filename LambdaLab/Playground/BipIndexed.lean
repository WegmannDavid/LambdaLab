import LambdaLab.Playground.Bip

/-!
# `IBip` — FIRST/FOLLOW in the *type*, and `do` notation restored

In `Bip.lean` the law rode in the structure, but `first`/`follow` were **fields**. That is why
there was no `bind`: the composite's `follow` must be `(k a).follow`, and `a` is a *runtime*
parse result, unavailable when constructing the structure.

Move them into the **type** and the problem dissolves. A continuation's type

    k : v → IBip f₂ fo₂ w v'

*asserts* that every `k a` has the same FIRST and FOLLOW. The uniformity condition that would
otherwise be a `by rfl` side-goal is now a **typing rule** — unstatable to violate. What it
rules out is a grammar whose *shape* depends on what it parsed, which is exactly the condition
LL parsing has always required; the typechecker now enforces it.

Consequences:
* `iBind` exists — genuinely **monadic**, with the seam as its *only* obligation.
* So `do`-notation comes back (`gdo` below), and the `(v × v')` pair-juggling of `bSeq`/`bMap`
  is gone.
* It is still not a `Bind` *instance*: the indices change (`IBip f₁ fo₁ → … → IBip f₁ fo₂`),
  and Lean's `Bind` needs one fixed `m`. This is an *indexed* (parameterised) monad, so it
  needs its own notation — but nothing more.

(Indices are `Char → Bool`. I tried a `CharClass` datatype to make seams `by decide`; it cost
more than it saved, because `Digit.ofChar?` is a match and `Char.isWhitespace` a disjunction —
neither is a char list, so every bridge lemma was Bool/List plumbing. The seams below are
one-liners anyway.)
-/

namespace Indexed

/-- FIRST and FOLLOW as **type indices**. -/
structure IBip (fst fol : Char → Bool) (w v : Type) where
  bp      : CBiparser w v
  firstOk : ∀ (c : Char) (rest : List Char), fst c = false → bp.run (c :: rest) = none
  ok      : RoundTrips bp (HeadIn fol)

variable {fst fol f₁ fo₁ f₂ fo₂ : Char → Bool} {w v v' : Type}

theorem IBip.noParse (p : IBip fst fol w v) (rest : List Char)
    (h : ∀ c, rest.head? = some c → fst c = false) : p.bp.run rest = none := by
  cases rest with
  | nil => exact run_nil _
  | cons c cs => exact p.firstOk c cs (h c rfl)

/-- **The payoff.** Every `IBip` round-trips terminally — no side-condition, no per-grammar
proof. `HeadIn f []` is vacuous, so end-of-input discharges the FOLLOW by itself. -/
theorem IBip.roundtrip (p : IBip fst fol w v) (s : w) :
    p.bp.run (p.bp.print s).2 = some ((p.bp.print s).1, []) := by
  have h := p.ok s [] (HeadIn_nil _)
  simpa using h

/-- A printed output always starts with a character in FIRST — *derived* from `ok` + `firstOk`,
not assumed. This is what lets `iBind` discharge its internal seam. -/
theorem IBip.head_first (q : IBip fst fol w v) (s : w) (rest : List Char)
    (hrest : HeadIn fol rest) (c : Char)
    (hc : ((q.bp.print s).2 ++ rest).head? = some c) : fst c = true := by
  cases hfc : fst c with
  | true => rfl
  | false =>
      exfalso
      have hnone : q.bp.run ((q.bp.print s).2 ++ rest) = none := by
        apply IBip.noParse
        intro c' hc'
        rw [hc] at hc'
        exact (Option.some.inj hc') ▸ hfc
      rw [q.ok s rest hrest] at hnone
      exact absurd hnone (by simp)

/-! ## Leaves -/

def iChar (c : Char) : IBip (· == c) (fun _ => true) w Char where
  bp := pChar1 c
  firstOk := by
    intro c' rest h
    have hne : ¬ (c' = c) := by simpa using h
    simp [CBiparser.run, pChar1, hne]
  ok := RoundTrips_mono (fun _ _ => trivial) (RoundTrips_pChar1 c)

def iDigit : IBip (fun c => (Digit.ofChar? c).isSome) (fun _ => true) Digit Digit where
  bp := digit1
  firstOk := by
    intro c rest h
    have hnone : Digit.ofChar? c = none := by
      cases hc : Digit.ofChar? c with
      | none => rfl
      | some d => rw [hc] at h; simp at h
    simp [CBiparser.run, digit1, hnone]
  ok := RoundTrips_mono (fun _ _ => trivial) RoundTrips_digit1

def iWs : IBip Char.isWhitespace (fun c => !c.isWhitespace) w Unit where
  bp := ws1
  firstOk := by
    intro c rest h
    simp [CBiparser.run, ws1, h]
  ok := RoundTrips_mono (fun _ hr c hc => by simpa using hr c hc) RoundTrips_ws1

/-! ## Combinators -/

def iMap (f : v → v') (p : IBip fst fol w v) : IBip fst fol w v' where
  bp := f <$> p.bp
  firstOk := by intro c rest h; simp [map_run, p.firstOk c rest h]
  ok := RoundTrips_map f p.bp _ p.ok

/-- **Monadic bind** — possible now, because `k`'s type pins its FIRST/FOLLOW independently of
the value. The seam is its one and only obligation. -/
def iBind (p : IBip f₁ fo₁ w v) (k : v → IBip f₂ fo₂ w v')
    (hseam : ∀ c, f₂ c = true → fo₁ c = true) : IBip f₁ fo₂ w v' where
  bp := p.bp >>= fun a => (k a).bp
  firstOk := by intro c rest h; simp [bind_run, p.firstOk c rest h]
  ok := by
    refine RoundTrips_bind p.bp _ (HeadIn fo₂) (HeadIn fo₁) p.ok (fun a => (k a).ok) ?_
    intro s rest hrest c hc
    exact hseam c ((k (p.bp.print s).1).head_first s rest hrest c hc)

/-- One-or-more. FOLLOW *computes*: the continuation may not start another element. `hrep`
("an element's own output may follow an element") is `fst ⊆ fol`. -/
def iMany1 (p : IBip fst fol w v) (hrep : ∀ c, fst c = true → fol c = true) :
    IBip fst (fun c => fol c && !fst c) (NEList w) (List v) where
  bp := many1NE p.bp
  firstOk := by intro c rest h; rw [many1NE_run_eq, p.firstOk c rest h]
  ok := by
    have hclosed : ∀ (s : w) (r : List Char),
        HeadIn fol r → HeadIn fol ((p.bp.print s).2 ++ r) := by
      intro s r hr c hc
      cases hout : (p.bp.print s).2 with
      | nil => rw [hout] at hc; simp at hc; exact hr c hc
      | cons c0 cs =>
          rw [hout] at hc; simp at hc
          subst hc
          exact hrep c0 (p.head_first s [] (HeadIn_nil _) c0 (by rw [hout]; rfl))
    refine RoundTrips_mono ?_ (RoundTrips_many1NE p.bp (HeadIn fol) p.ok hclosed)
    intro rest hr
    refine ⟨fun c hc => ?_, ?_⟩
    · have := hr c hc; simpa using (Bool.and_eq_true .. |>.mp this).1
    · apply IBip.noParse
      intro c hc
      have := hr c hc
      simpa using (Bool.and_eq_true .. |>.mp this).2

/-! ## `do`-notation, restored

`iBind` is an *indexed* monad, so Lean's `Bind`/`do` cannot apply — but a macro can. `gdo`
desugars exactly like `do1`, threading each seam as `(by seam)`. -/

/-- Discharges the lexical seam obligations. -/
macro "seam" : tactic => `(tactic| (
  intro c hc
  first
    | rfl
    -- whitespace may follow a digit run: whitespace is not a digit
    | (simp; exact ws_not_digit c hc)
    -- `;` may follow whitespace: `;` is not whitespace
    | (have hc' : c = ';' := by simpa using hc
       subst hc'; rfl)
    | simp_all))

syntax "gdo " ("let " ident " ← " term ";"?)+ "return " term : term

macro_rules
  | `(gdo $[let $xs ← $ps $[;]?]* return $e) => do
      let n := xs.size
      let mut acc ← `(iMap (fun $(xs[n-1]!) => $e) $(ps[n-1]!))
      for i in [0:n-1] do
        let j := n - 2 - i
        acc ← `(iBind $(ps[j]!) (fun $(xs[j]!) => $acc) (by seam))
      return acc

/-! ## The grammar — now a `do`-block again, and the round-trip is one line -/

def iDigits := iMany1 iDigit (by intro _ _; rfl)

def iElem := gdo
  let l  ← iDigits
  let _w ← iWs
  let _s ← iChar ';'
  return l

def iLists := iMany1 iElem (by intro _ _; rfl)

/-- **The end-to-end round-trip.** One line. -/
theorem iLists_roundtrip (s : (Digit × List Digit) × List (Digit × List Digit)) :
    iLists.bp.run (iLists.bp.print s).2 = some ((iLists.bp.print s).1, []) :=
  iLists.roundtrip s

#eval (iLists.bp.print ((.d1, [.d2]), [(.d3, [])])).2
#eval iLists.bp.run "12 ;3 ;".toList

end Indexed
