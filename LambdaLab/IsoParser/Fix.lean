import LambdaLab.IsoParser.Basic

/-!
# `fix` — recursion **with the law**

The recursor cannot be a law-carrying `IsoParser` (its law would only hold on shorter inputs;
bundling a partial law leaks a `sorry`). The honest design:

* the body is a **proof-free parse transformer** (`FixBody`), with the shortness guard inside the
  recursor — so ill-founded calls fail rather than loop, and no partial law is ever bundled;
* `print` is supplied as a plain **total function** — its recursion is the user's own
  (structurally recursive on the source), so the print side needs no fixpoint;
* the user proves **one step-law** (`hok`): *if the recursor satisfies the round-trip on strictly
  shorter print-inputs, the body satisfies it* — and `fix` runs the strong induction once,
  generically (`fixParse_run`).

So the wholesale induction a hand-written recursive parser needs is paid once, here; each grammar
pays only its one-layer step. The nested-parens validation at the bottom is the canonical
example.
-/

namespace LambdaLab.IsoParser

variable {α : Type} {fst fol : α → Prop} {w v : Type}

/-- A recursion body: one grammar layer, with a proof-free recursor (guard internalized). -/
abbrev FixBody (α : Type) (v : Type) :=
  (input : List α) →
    ((input' : List α) → Option (v × { r : List α // r.length < input'.length })) →
    Option (v × { r : List α // r.length < input.length })

-- `h` reads as unused: it is consumed only in `decreasing_by`.
set_option linter.unusedVariables false in
/-- Well-founded fixpoint with a proof-free recursor (guarded internally). -/
def fixParse (body : FixBody α v) :
    (input : List α) → Option (v × { r : List α // r.length < input.length })
  | input => body input (fun input' =>
      if h : input'.length < input.length then fixParse body input' else none)
termination_by input => input.length
decreasing_by exact h

/-- **The induction, paid once**: the step-law `hok` propagates the round-trip through the
fixpoint, by strong induction on the input length. -/
theorem fixParse_run (body : FixBody α v) (print : w → v × List α)
    (hok : ∀ (a : w) (rest : List α)
      (rec : (input' : List α) → Option (v × { r : List α // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (a' : w) (rest' : List α),
          ((print a').2 ++ rest').length < ((print a).2 ++ rest).length → HeadIn fol rest' →
          (rec ((print a').2 ++ rest')).map (fun z => (z.1, z.2.val)) = some ((print a').1, rest')) →
      (body ((print a).2 ++ rest) rec).map (fun z => (z.1, z.2.val)) = some ((print a).1, rest)) :
    ∀ (n : Nat) (a : w) (rest : List α), ((print a).2 ++ rest).length = n → HeadIn fol rest →
      (fixParse body ((print a).2 ++ rest)).map (fun z => (z.1, z.2.val))
        = some ((print a).1, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a rest hn hr
    rw [fixParse]
    apply hok a rest _ hr
    intro a' rest' hlt hr'
    simp only [dif_pos hlt]
    exact ih ((print a').2 ++ rest').length (hn ▸ hlt) a' rest' rfl hr'

/-- **The law-carrying fixpoint.** -/
def fix (body : FixBody α v) (print : w → v × List α)
    (hfirst : ∀ (c : α) (rest : List α) rec, ¬ fst c → body (c :: rest) rec = none)
    (hok : ∀ (a : w) (rest : List α)
      (rec : (input' : List α) → Option (v × { r : List α // r.length < input'.length })),
      HeadIn fol rest →
      (∀ (a' : w) (rest' : List α),
          ((print a').2 ++ rest').length < ((print a).2 ++ rest).length → HeadIn fol rest' →
          (rec ((print a').2 ++ rest')).map (fun z => (z.1, z.2.val)) = some ((print a').1, rest')) →
      (body ((print a).2 ++ rest) rec).map (fun z => (z.1, z.2.val)) = some ((print a).1, rest)) :
    IsoParser α fst fol w v where
  parse := fixParse body
  print := print
  firstOk c rest hc := by rw [fixParse, hfirst c rest _ hc]
  ok a rest hr := fixParse_run body print hok ((print a).2 ++ rest).length a rest rfl hr

/-! ## Validation: `P ::= 'a' | '(' P ')'`, source = value = nesting depth -/

/-- All the elements are equal, so a trailing copy commutes to the front. -/
theorem replicate_cons_comm (n : Nat) (a : α) (l : List α) :
    List.replicate n a ++ (a :: l) = a :: (List.replicate n a ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- The canonical string at depth `n` — the print side, structurally recursive on the source. -/
def wrap (n : Nat) : List Char :=
  List.replicate n '(' ++ ('a' :: List.replicate n ')')

/-- Peeling one nesting level, pre-associated into `print ++ continuation` shape. -/
theorem wrap_succ (n : Nat) (rest : List Char) :
    wrap (n + 1) ++ rest = '(' :: (wrap n ++ (')' :: rest)) := by
  simp [wrap, List.replicate_succ, List.append_assoc, replicate_cons_comm]

/-- One grammar layer, proof-free recursor. -/
def parensBody : FixBody Char Nat := fun input rec =>
  match input with
  | [] => none
  | c :: rest =>
    if c = 'a' then some (0, ⟨rest, by simp⟩)
    else if c = '(' then
      match rec rest with
      | some (n, r) =>
        match hr : r.val with
        | ')' :: r2 => some (n + 1, ⟨r2, by
            have h0 := r.property; rw [hr] at h0
            simp only [List.length_cons] at h0 ⊢; omega⟩)
        | _ => none
      | none => none
    else none

/-- **Nested parens, with the round-trip law**: the step-law is one layer of the induction. -/
def pParens : IsoParser Char (fun c => c = 'a' ∨ c = '(') (fun _ => True) Nat Nat :=
  fix parensBody (fun n => (n, wrap n))
    (hfirst := by
      intro c rest rec hc
      have h1 : ¬ c = 'a' := fun h => hc (Or.inl h)
      have h2 : ¬ c = '(' := fun h => hc (Or.inr h)
      simp only [parensBody]; rw [if_neg h1, if_neg h2])
    (hok := by
      intro a rest rec _ hrec
      cases a with
      | zero =>
        show (parensBody ('a' :: rest) rec).map (fun z => (z.1, z.2.val)) = some (0, rest)
        simp [parensBody]
      | succ m =>
        show (parensBody (wrap (m + 1) ++ rest) rec).map (fun z => (z.1, z.2.val))
          = some (m + 1, rest)
        rw [wrap_succ]
        simp only [parensBody]
        rw [if_neg (by decide)]; simp only [if_true]
        have hq : (rec (wrap m ++ (')' :: rest))).map (fun z => (z.1, z.2.val))
            = some (m, ')' :: rest) :=
          hrec m (')' :: rest)
            (by simp only [wrap, List.length_append, List.length_cons,
                  List.length_replicate]; omega)
            (by intro c _; trivial)
        rcases hrc : rec (wrap m ++ (')' :: rest)) with _ | ⟨n', r0⟩
        · rw [hrc] at hq; simp at hq
        · rw [hrc] at hq
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
          obtain ⟨rfl, hrv⟩ := hq
          obtain ⟨r0v, r0lt⟩ := r0
          subst hrv
          rfl)

#eval pParens.run "((a))".toList  -- some (2, [])
#eval pParens.run "((a)".toList   -- none
#eval (pParens.print 3).2         -- ['(', '(', '(', 'a', ')', ')', ')']

/-- The round-trip — a theorem, free. -/
example (n : Nat) : pParens.run (pParens.print n).2 = some ((pParens.print n).1, []) :=
  pParens.roundtrip n

end LambdaLab.IsoParser
