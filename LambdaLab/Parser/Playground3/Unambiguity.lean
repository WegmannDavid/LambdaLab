import LambdaLab.Parser.Playground3.Verified
import LambdaLab.Parser.Playground3.Example
import LambdaLab.Parser.Playground3.Ambiguity

/-!
# Sufficient conditions for unambiguity: unique name parts

`Grammar` deliberately admits ambiguous grammars (the parser returns all
parses); uniqueness is recovered *conditionally*. This file fixes the
condition, following Danielsson–Norell, *Parsing Mixfix Operators*, §4
(`literature/danielsson-norell-mixfix.pdf`):

> if all operator name parts in a precedence graph are unique, then the
> resulting grammar is unambiguous

(together with acyclicity, which `Grammar.tighter_wf` already provides; the
remaining structural requirements of the paper — at least one name part, no
adjacent holes, no adjacent name parts — are enforced by construction in
`Operator`/`Part.inner`).

`Grammar.UniqueNameParts` is the user-facing certificate: a per-grammar,
finitely-checkable condition (`arith_uniqueNameParts` below is discharged by
`cases`+`simp`). The counterexample grammar of `Ambiguity.lean` fails it
exactly at the token reuse that made it ambiguous
(`amb_not_uniqueNameParts`).

The implication `unambiguous_of_uniqueNameParts` is *stated* here with the
supporting counting lemma proved (`count_flatten_expr`: under unique name
parts, a token occurs in a flattening exactly as often as its owning operator
is applied). The full proof is future work; the paper only sketches it
(reduction to Lotfallah 2009 via Aasa's "generalised brackets"), and its Agda
formalization does not include it. Roadmap for our closed/non-assoc-infix
fragment, on top of `count_flatten_expr`:

1. *Bracket counting*: for adjacent name tokens `t_i, t_{i+1}` of one
   operator, every prefix of a flattening satisfies
   `count t_i ≥ count t_{i+1}` (openers before closers).
2. *Segmentation*: two trees flattening to the same string place their body
   tokens at the same positions — a hole that ends earlier in one parse than
   the other puts the follow token inside the other parse's hole, breaking 1.
3. *Split uniqueness for infix tops*: a token occurrence at "bracket depth 0"
   lies on the outer spine, so two different infix splits of one string give
   `Tighter`-paths in both directions between the two top operators — a cycle,
   contradicting `tighter_wf`.
-/

namespace LambdaLab.Parser.Playground3

open LambdaLab.Parser

variable {G : Grammar}

/-! ## The condition -/

/-- **Unique name parts** (Danielsson–Norell §4): every token is a name part
of at most one operator, at most once. The opt-in certificate a grammar
author provides to obtain uniqueness of parses; grammars violating it are
still perfectly usable through the all-parses interface. -/
structure Grammar.UniqueNameParts (G : Grammar) : Prop where
  /-- No operator repeats a name part within its own body. -/
  nodup : ∀ o : G.Op, (G.operator o).nameTokens.Nodup
  /-- A name part determines its operator. -/
  owner : ∀ o₁ o₂ : G.Op, ∀ t : Token,
    t ∈ (G.operator o₁).nameTokens → t ∈ (G.operator o₂).nameTokens → o₁ = o₂

/-! ## Counting applications

The engine of the unambiguity proof: with unique name parts, occurrences of a
token in a flattening are in bijection with applications of its owning
operator. -/

/-- The name tokens contributed by a body segment (holes contribute none). -/
def Part.bodyTokens : List (Part G) → List Token
  | [] => []
  | .namePart t :: ps => t :: bodyTokens ps
  | .hole _ :: ps => bodyTokens ps

theorem Part.bodyTokens_append (ps qs : List (Part G)) :
    Part.bodyTokens (ps ++ qs) = Part.bodyTokens ps ++ Part.bodyTokens qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [Part.bodyTokens, ih]

theorem Part.bodyTokens_inner (tkns : NonEmptyList Token) :
    Part.bodyTokens (G := G) (Part.inner tkns) = tkns.toList := by
  induction tkns with
  | last t => rfl
  | cons t ts ih => simp [Part.inner, Part.bodyTokens, NonEmptyList.toList, ih]

/-- A full operator body contributes exactly the operator's name tokens. -/
theorem Part.bodyTokens_parts (o : G.Op) :
    Part.bodyTokens (Part.parts o) = (G.operator o).nameTokens := by
  unfold Part.parts Operator.nameTokens
  cases G.operator o with
  | closed tkns => exact Part.bodyTokens_inner tkns
  | prefx tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_append, Part.bodyTokens_inner]
  | infx tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_append, Part.bodyTokens_inner]

mutual
  /-- The number of applications of operator `o` in an expression. -/
  def Expr.countApps [DecidableEq G.Op] (o : G.Op) {l : Level G} : Expr G l → Nat
    | .op o' _ parts => (if o' = o then 1 else 0) + parts.countApps o

  /-- The number of applications of operator `o` in a body segment. -/
  def Parts.countApps [DecidableEq G.Op] (o : G.Op) {ps : List (Part G)} : Parts G ps → Nat
    | .nil => 0
    | .hole e p => e.countApps o + p.countApps o
    | .namePart _ p => p.countApps o
end

/-- In a duplicate-free list, a member is counted exactly once. -/
theorem List.count_eq_one_of_nodup_mem {α : Type _} [DecidableEq α]
    {l : List α} {a : α} (hd : l.Nodup) (hm : a ∈ l) : l.count a = 1 := by
  induction l with
  | nil => cases hm
  | cons x xs ih =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · have hx : a ∉ xs := (List.nodup_cons.mp hd).1
        simp [List.count_eq_zero.mpr hx]
      · have hne : x ≠ a := fun h => (List.nodup_cons.mp hd).1 (h ▸ hm')
        simp [hne, ih (List.nodup_cons.mp hd).2 hm']

mutual
  /-- **Occurrence counting**: under unique name parts, a name token of `o`
  occurs in `e.flatten` exactly as often as `o` is applied in `e`. In
  particular every token occurrence in a flattening is "owned" by a unique
  application — the formal core of Aasa's generalised-brackets view. -/
  theorem count_flatten_expr [DecidableEq G.Op] (h : G.UniqueNameParts) {o : G.Op}
      {t : Token} (ht : t ∈ (G.operator o).nameTokens) {l : Level G} (e : Expr G l) :
      e.flatten.count t = e.countApps o :=
    match e with
    | .op o' _ parts => by
        rw [Expr.flatten_op, Expr.countApps, count_flatten_parts h ht parts,
          Part.bodyTokens_parts]
        congr 1
        by_cases ho : o' = o
        · subst ho
          rw [if_pos rfl]
          exact List.count_eq_one_of_nodup_mem (h.nodup o') ht
        · rw [if_neg ho]
          exact List.count_eq_zero.mpr (fun hmem => ho (h.owner o' o t hmem ht))

  /-- Body-segment version: token occurrences split into the segment's own
  name tokens plus the holes' contributions. -/
  theorem count_flatten_parts [DecidableEq G.Op] (h : G.UniqueNameParts) {o : G.Op}
      {t : Token} (ht : t ∈ (G.operator o).nameTokens) {ps : List (Part G)}
      (p : Parts G ps) :
      p.flatten.count t = (Part.bodyTokens ps).count t + p.countApps o :=
    match ps, p with
    | _, .nil => rfl
    | _, .hole e p' => by
        rw [Parts.flatten_hole, List.count_append, count_flatten_expr h ht e,
          count_flatten_parts h ht p', Parts.countApps, Part.bodyTokens]
        omega
    | _, .namePart tk p' => by
        rw [Parts.flatten_namePart, List.count_cons, count_flatten_parts h ht p',
          Part.bodyTokens, List.count_cons, Parts.countApps]
        omega
end

/-! ## Witnesses -/

/-- `arith` has unique name parts: `n`, `(`, `)`, `+`, `*` each belong to one
operator, once. -/
theorem arith_uniqueNameParts : arith.UniqueNameParts where
  nodup o := by
    cases o <;> simp [symOp, Operator.nameTokens, NonEmptyList.toList]
  owner o₁ o₂ t h₁ h₂ := by
    cases o₁ <;> cases o₂ <;>
      simp_all [symOp, Operator.nameTokens, NonEmptyList.toList]

/-- The ambiguous grammar of `Ambiguity.lean` fails the condition exactly at
the reused `*`: it is a name part of both `wrap` and `mul`. -/
theorem amb_not_uniqueNameParts : ¬ amb.UniqueNameParts := fun h =>
  AmbOp.noConfusion (h.owner .wrap .mul "*"
    (by simp [ambOperator, Operator.nameTokens, NonEmptyList.toList])
    (by simp [ambOperator, Operator.nameTokens, NonEmptyList.toList]))

/-! ## The target theorem -/

/-- **Unique name parts give unambiguity** (Danielsson–Norell §4, specialized
to the closed/non-assoc-infix fragment). Together with `parse_unique` this
yields: for a grammar certified by `UniqueNameParts`, `parse` returns (copies
of) at most one tree.

Proof is future work — see the module docstring for the roadmap; the
counterexample `amb_not_uniqueNameParts` shows the hypothesis is doing real
work. -/
theorem unambiguous_of_uniqueNameParts (h : G.UniqueNameParts) : G.Unambiguous := by
  sorry

end LambdaLab.Parser.Playground3
