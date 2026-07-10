import LambdaLab.Biparser.Mixfix.RightSublist

/-!
# A concrete deterministic mixfix biparser — the verified blueprint

A fully verified, hand-rolled deterministic parser + printer for the smallest
grammar that is *structurally faithful* to the general case:

    e ::= t | t '+' e        (right-associative infix — the open-operator case)
    t ::= x | '(' e ')'      (a variable, or parens — the closed / loosest-recursion case)

This validates the whole Phase 3/4 approach before the generic dependent version:

* **Termination**: the leftover is a `RightSublist input` (progress witness), so the
  infix right-operand recursion — which recurses on a *parse result's* leftover —
  terminates (`termination_by 2 * input.length + level`). A plain `List` leftover
  cannot: `termination_by` can't see `rest2.length < input.length`.
* **Deterministic dispatch** via explicit `if` (not char-literal patterns, which
  `split` can't reduce).
* **Conditional round trip** (`Tm_rt`/`Ex_rt`): a *term* round-trips at any `rest`
  (it is delimited), an *expression* round-trips when `rest` doesn't start with `'+'`
  (else greedy parsing would grab it) — the "distinct-leading-token" obligation, here
  discharged from the grammar's shape. `terminal_rt` is the `rest = []` corollary.

The general version generalizes this to an arbitrary `Grammar`, replacing `Ex`/`Tm`
with the dependent `Expr`/`Parts` and the `'+'`/`'('` dispatch with the
`headsDistinct` grammar condition. `[propext, Quot.sound]`, no sorries.
-/

namespace LambdaLab.Biparser.Mixfix.Concrete

open LambdaLab.Biparser.Mixfix (RightSublist)
open RightSublist (consTail)

/-! ## Syntax trees and their canonical print -/

mutual
inductive Ex | ofTerm : Tm → Ex | add : Tm → Ex → Ex
inductive Tm | var : Char → Tm | paren : Ex → Tm
end

mutual
def Ex.print : Ex → List Char
  | .ofTerm t => t.print
  | .add t e  => t.print ++ '+' :: e.print
def Tm.print : Tm → List Char
  | .var c   => [c]
  | .paren e => '(' :: e.print ++ [')']
end

/-! ## The deterministic parser (hand-rolled spine, `RightSublist` for termination) -/

mutual
def parseEx (input : List Char) : Option (Ex × RightSublist input) :=
  match parseTm input with
  | none => none
  | some (t, s1) =>
      match hs : s1.list with
      | [] => some (.ofTerm t, s1)
      | c :: rest2 =>
          if c = '+' then
            have hprog : rest2.length < input.length := by
              have := s1.lt; rw [hs] at this; simp at this; omega
            match parseEx rest2 with
            | some (e, s2) => some (.add t e, ⟨s2.list, Nat.lt_trans s2.lt hprog⟩)
            | none => none
          else some (.ofTerm t, s1)
  termination_by 2 * input.length + 1
  decreasing_by all_goals omega

def parseTm (input : List Char) : Option (Tm × RightSublist input) :=
  match input with
  | [] => none
  | c :: rest =>
      if c = '(' then
        match parseEx rest with
        | none => none
        | some (e, s1) =>
            match hs : s1.list with
            | [] => none
            | c2 :: rest2 =>
                if c2 = ')' then
                  some (.paren e, ⟨rest2, by
                    have := s1.lt; rw [hs] at this; simp at this
                    simp only [List.length_cons]; omega⟩)
                else none
      else if c.isAlpha then some (.var c, consTail c rest)
      else none
  termination_by 2 * input.length
  decreasing_by simp only [List.length_cons]; omega
end

def parse (s : String) : Option Ex := (parseEx s.toList).map (·.1)
#eval (parse "a+b+c").isSome     -- true
#eval (parse "(a+b)+c").isSome   -- true
#eval (parse "a+(b").isSome      -- false
#eval (parse "()").isSome        -- false

/-! ## Round-trip proof

`parseEx`/`parseTm` have dependent return types (`RightSublist input`), so `rw`/`simp`
cannot rewrite their argument; `*_cast` transports a result along an input equality. -/

theorem parseEx_cast {a b : List Char} (hab : a = b) {e : Ex} {s : RightSublist b}
    (hp : parseEx b = some (e, s)) : ∃ s', parseEx a = some (e, s') ∧ s'.list = s.list := by
  subst hab; exact ⟨s, hp, rfl⟩

theorem parseTm_cast {a b : List Char} (hab : a = b) {t : Tm} {s : RightSublist b}
    (hp : parseTm b = some (t, s)) : ∃ s', parseTm a = some (t, s') ∧ s'.list = s.list := by
  subst hab; exact ⟨s, hp, rfl⟩

/-! Well-formedness: variables are letters (the concrete grammar's `isVar`). -/
mutual
def Ex.wf : Ex → Prop
  | .ofTerm t => t.wf
  | .add t e  => t.wf ∧ e.wf
def Tm.wf : Tm → Prop
  | .var c   => c.isAlpha = true
  | .paren e => e.wf
end

mutual
/-- A well-formed **term** round-trips at *any* continuation (it is delimited). -/
theorem Tm_rt (t : Tm) (h : t.wf) (rest : List Char) :
    ∃ s, parseTm (t.print ++ rest) = some (t, s) ∧ s.list = rest := by
  cases t with
  | var c =>
      simp only [Tm.wf] at h
      have hne : c ≠ '(' := by intro heq; subst heq; simp at h
      refine ⟨consTail c rest, ?_, rfl⟩
      rw [parseTm.eq_def]; simp only [Tm.print, List.singleton_append]
      simp [hne, h]
  | paren e =>
      simp only [Tm.wf] at h
      obtain ⟨s, hpe, hsl⟩ := Ex_rt e h (')' :: rest) (by simp)
      have hn : (e.print ++ [')']) ++ rest = e.print ++ ')' :: rest := by rw [List.append_assoc]; rfl
      obtain ⟨s', hpe', hsl'⟩ := parseEx_cast hn hpe
      refine ⟨⟨rest, by simp [Tm.print]; omega⟩, ?_, rfl⟩
      have hs'l : s'.list = ')' :: rest := hsl'.trans hsl
      rw [parseTm.eq_def]
      simp only [Tm.print, List.cons_append, hpe', if_true]
      split
      · rename_i heq; rw [hs'l] at heq; simp at heq
      · rename_i c2 rest2 heq
        rw [hs'l] at heq; obtain ⟨rfl, rfl⟩ := List.cons.inj heq; simp
/-- A well-formed **expression** round-trips when `rest` doesn't start with `'+'`. -/
theorem Ex_rt (e : Ex) (h : e.wf) (rest : List Char) (hr : rest.head? ≠ some '+') :
    ∃ s, parseEx (e.print ++ rest) = some (e, s) ∧ s.list = rest := by
  cases e with
  | ofTerm t =>
      simp only [Ex.wf] at h
      obtain ⟨s, hpt, hsl⟩ := Tm_rt t h rest
      refine ⟨s, ?_, hsl⟩
      rw [parseEx.eq_def]; simp only [Ex.print, hpt]
      split
      · rfl
      · rename_i c rest2 hs
        have hc : c ≠ '+' := by rw [hsl] at hs; rw [hs] at hr; simpa using hr
        simp [hc]
  | add t e =>
      simp only [Ex.wf] at h
      obtain ⟨s1, hpt, hsl⟩ := Tm_rt t h.1 ('+' :: (e.print ++ rest))
      have hnt : t.print ++ '+' :: e.print ++ rest = t.print ++ '+' :: (e.print ++ rest) := by
        rw [List.append_assoc]; rfl
      obtain ⟨s1', hpt', hsl'⟩ := parseTm_cast hnt hpt
      obtain ⟨s2, hpe, hsl2⟩ := Ex_rt e h.2 rest hr
      have hs1l : s1'.list = '+' :: (e.print ++ rest) := hsl'.trans hsl
      refine ⟨⟨s2.list, ?_⟩, ?_, hsl2⟩
      · have := s2.lt
        simp only [Ex.print, List.length_append, List.length_cons] at this ⊢
        omega
      · rw [parseEx.eq_def]
        simp only [Ex.print, hpt']
        split
        · rename_i heq; rw [hs1l] at heq; simp at heq
        · rename_i c rest2 heq
          rw [hs1l] at heq; obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          simp [hpe]
end

/-- **Terminal round trip**: printing a well-formed tree and parsing it back
recovers the tree exactly, with nothing left over. -/
theorem terminal_rt (e : Ex) (h : e.wf) :
    ∃ s, parseEx e.print = some (e, s) ∧ s.list = [] := by
  have hh := Ex_rt e h [] (by simp); rw [List.append_nil] at hh; exact hh

end LambdaLab.Biparser.Mixfix.Concrete
