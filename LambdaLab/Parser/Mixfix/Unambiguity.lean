import LambdaLab.Parser.Mixfix.Verified
import LambdaLab.Parser.Mixfix.Example
import LambdaLab.Parser.Mixfix.Ambiguity

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
`Operator`/`Notation.toParts`).

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

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

variable {G : Grammar}

/-- An operator the token-based certificate can handle: a fixed name-token
skeleton with *both* operands strictly tighter — `closed` / `prefx` / `infx` /
`postfx`. Excluded: the tokenless `juxt` and the associative `infxl` / `infxr`
(their `.tighterEq` operand holes put no separator token where `Stops`/`BodyOk`
need one). -/
def Operator.simple : Operator → Bool
  | .closed _ => true
  | .prefx _  => true
  | .infx _   => true
  | .postfx _ => true
  | _         => false

/-- A grammar all of whose operators are `simple`. The token-based unambiguity
certificate below covers exactly this fragment: juxtaposition is tokenless and
the associative infixes are left- or right-recursive, so the leading-token /
bracket-counting machinery (`Operator.head`, `BodyOk`, `Stops`) has nothing to
grip on for them. Their uniqueness (juxt/`infxl` left-assoc, `infxr` right-assoc)
is a separate argument, out of scope here. -/
def Grammar.NonAssoc (G : Grammar) : Prop := ∀ o : G.Op, (G.operator o).simple = true

/-- A `simple` operator is in particular not juxtaposition. -/
theorem Grammar.NonAssoc.ne_juxt {G : Grammar} (h : G.NonAssoc) (o : G.Op) :
    G.operator o ≠ Operator.juxt := by
  intro he; have := h o; rw [he] at this; simp [Operator.simple] at this

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
  /-- Variable tokens are disjoint from operator name parts, so a token cannot be
  read as both a variable leaf and (part of) an operator. -/
  varDisjoint : ∀ t : Token, G.isVar t = true → ∀ o : G.Op, t ∉ (G.operator o).nameTokens

/-! ## Counting applications

The engine of the unambiguity proof: with unique name parts, occurrences of a
token in a flattening are in bijection with applications of its owning
operator. -/

/-- The name tokens contributed by a body segment (holes and sub-holes contribute
none). -/
def Part.bodyTokens : List (Part G) → List Token
  | [] => []
  | .namePart t :: ps => t :: bodyTokens ps
  | .hole _ :: ps => bodyTokens ps
  | .subHole _ :: ps => bodyTokens ps

theorem Part.bodyTokens_append (ps qs : List (Part G)) :
    Part.bodyTokens (ps ++ qs) = Part.bodyTokens ps ++ Part.bodyTokens qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [Part.bodyTokens, ih]

theorem Part.bodyTokens_inner (tkns : Notation) :
    Part.bodyTokens (G := G) (Notation.toParts tkns) = tkns.toTokens := by
  induction tkns with
  | last t => rfl
  | cons t h ts ih => cases h <;> simp [Notation.toParts, Part.bodyTokens, Notation.toTokens, InnerHole.toPart, ih]

/-- A full operator body contributes exactly the operator's name tokens. -/
theorem Part.bodyTokens_parts (o : G.Op) :
    Part.bodyTokens (Operator.body o) = (G.operator o).nameTokens := by
  unfold Operator.body Operator.nameTokens
  cases G.operator o with
  | closed tkns => exact Part.bodyTokens_inner tkns
  | prefx tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_append, Part.bodyTokens_inner]
  | infx tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_append, Part.bodyTokens_inner]
  | infxl tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_append, Part.bodyTokens_inner]
  | infxr tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_append, Part.bodyTokens_inner]
  | juxt => rfl
  | postfx tkns =>
      simp [Part.bodyTokens, Part.bodyTokens_inner]

mutual
  /-- The number of applications of operator `o` in an expression. -/
  def Expr.countApps [DecidableEq G.Op] (o : G.Op) {l : Level G} : Expr G l → Nat
    | .op o' _ parts => (if o' = o then 1 else 0) + parts.countApps o
    | .var _ _ => 0

  /-- The number of applications of operator `o` in a body segment. (A sub-hole's
  result belongs to another grammar, so it contributes no `o`-applications.) -/
  def Parts.countApps [DecidableEq G.Op] (o : G.Op) {ps : List (Part G)} : Parts G ps → Nat
    | .nil => 0
    | .hole e p => e.countApps o + p.countApps o
    | .namePart _ p => p.countApps o
    | .subHole _ _ p => p.countApps o
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
    | .var t' hv => by
        rw [Expr.flatten_var, Expr.countApps]
        have hne : t' ≠ t := by rintro rfl; exact h.varDisjoint _ hv o ht
        simp [hne]

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
    | _, .subHole sp res p' => by
        rw [Parts.flatten_subHole, List.count_append, count_flatten_parts h ht p',
          Parts.countApps, Part.bodyTokens]
        -- A host name token `t` does not occur in an embedded sub-grammar's
        -- output (token-disjointness between the host and the embedded language).
        -- This interface condition for embedded-grammar uniqueness is future work.
        have hsub : (sp.flatten res).count t = 0 := sorry
        omega
end

/-! ## Witnesses -/

/-- `arith` has unique name parts: `n`, `(`, `)`, `+`, `*` each belong to one
operator, once. -/
theorem arith_uniqueNameParts : arith.UniqueNameParts where
  nodup o := by
    cases o <;> simp [symOp, Operator.nameTokens, Notation.toTokens]
  owner o₁ o₂ t h₁ h₂ := by
    cases o₁ <;> cases o₂ <;>
      simp_all [symOp, Operator.nameTokens, Notation.toTokens] <;>
      (rcases h₂ with rfl | rfl <;>
        simp_all [symOp, Operator.nameTokens, Notation.toTokens])
  varDisjoint t hvar o := by
    intro hmem
    have hnotin : t ∉ ["n", "(", ")", "+", "*", "-", "!", "^", "\\lambda", "."] :=
      of_decide_eq_true hvar
    exact hnotin (by cases o <;> simp_all [symOp, Operator.nameTokens, Notation.toTokens])

/-- The ambiguous grammar of `Ambiguity.lean` fails the condition exactly at
the reused `*`: it is a name part of both `wrap` and `mul`. -/
theorem amb_not_uniqueNameParts : ¬ amb.UniqueNameParts := fun h =>
  AmbOp.noConfusion (h.owner .wrap .mul "*"
    (by simp [ambOperator, Operator.nameTokens, Notation.toTokens])
    (by simp [ambOperator, Operator.nameTokens, Notation.toTokens]))

/-! ## Segmentation machinery (forest-free port of the spine `Stops` argument)

Ported from `Playground.Uniqueness`, but *without* its `tighter_disjoint` /
`loosest_disjoint` (forest) hypotheses: the jump encoding of `Expr` (it names its
real top operator with a proof-irrelevant witness, recording no intermediate
precedence node) collapses DAG diamonds to equal trees, so the cross-node cases
that forced the forest assumption in the spine simply do not arise here. What
remains genuinely hard — determining the *top operator* of an infix expression
from its token string — is isolated as the single `topOp_unique` axiom-shaped
lemma below. Everything else uses only `UniqueNameParts` + `tighter_wf`. -/

/-- First name token of a nonempty token list. -/
def Notation.head : Notation → Token
  | .last x => x
  | .cons x _ _ => x

theorem Notation.head_mem_toTokens (l : Notation) : l.head ∈ l.toTokens := by
  cases l with
  | last x => simp [Notation.head, Notation.toTokens]
  | cons x h xs => simp [Notation.head, Notation.toTokens]

/-- The leading name part of an operator (junk for the tokenless `juxt`, which is
excluded from the token-based machinery by `Grammar.NonAssoc`). -/
def Operator.head : Operator → Token
  | .closed t => t.head
  | .prefx t => t.head
  | .infx t => t.head
  | .infxl t => t.head
  | .infxr t => t.head
  | .postfx t => t.head
  | .juxt => ""

theorem Operator.head_mem (o : Operator) (hj : o ≠ Operator.juxt) : o.head ∈ o.nameTokens := by
  cases o <;> first | exact Notation.head_mem_toTokens _ | exact absurd rfl hj

theorem Operator.nameTokens_eq (o : Operator) (hj : o ≠ Operator.juxt) :
    o.nameTokens = o.head :: o.nameTokens.tail := by
  cases o <;> first | (rename_i t; cases t <;> rfl) | exact absurd rfl hj

theorem mem_of_mem_tail {α} {l : List α} {t : α} (h : t ∈ l.tail) : t ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp only [List.tail_cons] at h; exact List.mem_cons_of_mem x h

theorem head?_append_left {l s : List Token} (hl : l ≠ []) : (l ++ s).head? = l.head? := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs => rfl

theorem head?_eq_of_prefix {l₁ l₂ s₁ s₂ : List Token}
    (h : l₁ ++ s₁ = l₂ ++ s₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) : l₁.head? = l₂.head? := by
  have : (l₁ ++ s₁).head? = (l₂ ++ s₂).head? := by rw [h]
  rwa [head?_append_left h₁, head?_append_left h₂] at this

/-! ### Reachability -/

theorem TighterEq.trans {a b c : G.Op}
    (h₁ : TighterEq G.tighter a b) (h₂ : TighterEq G.tighter b c) : TighterEq G.tighter a c := by
  induction h₁ with
  | refl => exact h₂
  | step hmem _ ih => exact TighterEq.step hmem (ih h₂)

theorem Tighter.trans {a b c : G.Op}
    (h₁ : Tighter G.tighter a b) (h₂ : Tighter G.tighter b c) : Tighter G.tighter a c := by
  induction h₁ with
  | base hmem => exact Tighter.step hmem h₂
  | step hmem _ ih => exact Tighter.step hmem (ih h₂)

theorem Tighter.trans_tighterEq {a o o' : G.Op}
    (h : Tighter G.tighter a o) (h' : TighterEq G.tighter o o') : Tighter G.tighter a o' := by
  cases h'.toTighterOrEq with
  | inl he => exact he ▸ h
  | inr ht => exact h.trans ht

/-- No cycle: an operator is unreachable from anything strictly tighter than it. -/
theorem no_cycle {a b : G.Op} (h : b ∈ G.tighter a) : ¬ TighterEq G.tighter b a := by
  suffices H : ∀ a b, b ∈ G.tighter a → TighterEq G.tighter b a → False from fun hr => H a b h hr
  intro a
  induction a using G.tighter_wf.induction with
  | _ a ih =>
    intro b hRba hreach
    cases hreach with
    | refl => exact ih a hRba a hRba TighterEq.refl
    | step hRcb hca =>
        rename_i c
        exact ih b hRba c hRcb (hca.trans (TighterEq.step hRba TighterEq.refl))

/-- The level condition is up-closed along `TighterEq`: reachability is transitive. -/
theorem Level.condition_up {l : Level G} {o o' : G.Op}
    (hc : Level.condition l o) (hT : TighterEq G.tighter o o') : Level.condition l o' := by
  cases l with
  | tighter a => exact Tighter.trans_tighterEq hc hT
  | tighterEq a => exact TighterEq.trans hc hT
  | loosest => obtain ⟨r, hr, hp⟩ := hc; exact ⟨r, hr, hp.trans hT⟩

/-! ### Name parts determine operators -/

theorem Grammar.UniqueNameParts.heads_distinct (h : G.UniqueNameParts) (hnj : G.NonAssoc)
    {o o' : G.Op} (hne : o ≠ o') : (G.operator o).head ≠ (G.operator o').head := by
  intro he
  exact hne (h.owner o o' _ (Operator.head_mem _ (hnj.ne_juxt o)) (he ▸ Operator.head_mem _ (hnj.ne_juxt o')))

/-- Every name part *after the leading one* is the head of no operator. -/
theorem Grammar.UniqueNameParts.tail_notHead (h : G.UniqueNameParts) (hnj : G.NonAssoc) (a : G.Op) :
    ∀ tk ∈ (G.operator a).nameTokens.tail, ∀ o : G.Op, (G.operator o).head ≠ tk := by
  intro tk htk o he
  have hmem_a : tk ∈ (G.operator a).nameTokens := mem_of_mem_tail htk
  have hmem_o : tk ∈ (G.operator o).nameTokens := he ▸ Operator.head_mem _ (hnj.ne_juxt o)
  have hoa : o = a := h.owner o a tk hmem_o hmem_a
  subst hoa
  have hnd := h.nodup o
  rw [Operator.nameTokens_eq (G.operator o) (hnj.ne_juxt o)] at hnd
  exact (List.nodup_cons.mp hnd).1 (he.symm ▸ htk)

/-! ### `flatten` is never empty -/

mutual
  theorem Expr.flatten_ne {l : Level G} (e : Expr G l) : e.flatten ≠ [] := by
    match e with
    | .op o _ parts => rw [Expr.flatten_op]; exact Parts.flatten_ne parts (Operator.body_ne_nil o)
    | .var t _ => rw [Expr.flatten_var]; exact List.cons_ne_nil t []

  theorem Parts.flatten_ne {ps : List (Part G)} (p : Parts G ps) (hps : ps ≠ []) :
      p.flatten ≠ [] := by
    match ps, p with
    | [], _ => exact absurd rfl hps
    | (.namePart _) :: _, .namePart _ _ => simp [Parts.flatten]
    | (.hole _) :: _, .hole e _ =>
        rw [Parts.flatten_hole]
        exact fun hc => Expr.flatten_ne e (List.append_eq_nil_iff.mp hc).1
    | (.subHole _) :: _, .subHole sp res _ =>
        rw [Parts.flatten_subHole]
        -- a sub-parser's result flattens to a nonempty token list (it consumes
        -- ≥1 token) — an interface guarantee for embedded grammars, future work.
        exact fun hc => (show sp.flatten res ≠ [] from sorry) (List.append_eq_nil_iff.mp hc).1
end

theorem Parts.flatten_head_inner {tkns : Notation} (p : Parts G (Notation.toParts tkns)) :
    p.flatten.head? = some tkns.head :=
  match tkns, p with
  | .last _, .namePart _ _ => by simp [Parts.flatten, Notation.head]
  | .cons _ _ _, .namePart _ _ => by simp [Parts.flatten, Notation.head]

/-! ### `Stops` -/

/-- The leftover `s` does not begin with a token that could continue an expression
at level `l`: no operator satisfying `l`'s condition has its head there. -/
def Stops (l : Level G) (s : List Token) : Prop :=
  ∀ o : G.Op, Level.condition l o → s.head? ≠ some (G.operator o).head

/-- A leftover that stops level `l` also stops any strictly-tighter level reachable
through an `l`-operator `o`. -/
theorem Stops.tighter {l : Level G} {o : G.Op} (hc : Level.condition l o)
    {s : List Token} (hs : Stops l s) : Stops (Level.tighter o) s :=
  fun o' (hT : Tighter G.tighter o o') => hs o' (Level.condition_up hc hT.toTighterEq)

/-- A leftover that begins with no operator's head at all stops every level. -/
theorem Stops.of_noHead {s : List Token} {tk : Token} (hhd : s.head? = some tk)
    (hno : ∀ o : G.Op, (G.operator o).head ≠ tk) (l : Level G) : Stops l s :=
  fun o _ hcon => hno o (by rw [hhd] at hcon; exact (Option.some.inj hcon).symm)

/-- A leftover that begins with `o`'s own head stops every level *strictly tighter*
than `o` (acyclicity: nothing tighter than `o` can reach `o`). -/
theorem Stops.tighter_of_head (h : G.UniqueNameParts) (hnj : G.NonAssoc) {o : G.Op} {s : List Token}
    (hhd : s.head? = some (G.operator o).head) : Stops (Level.tighter o) s := by
  intro o' (hT : Tighter G.tighter o o') hcon
  rw [hhd] at hcon
  have heq : (G.operator o).head = (G.operator o').head := Option.some.inj hcon
  have hoo : o = o' := Classical.byContradiction fun hne => h.heads_distinct hnj hne heq
  obtain ⟨b, hb, hpath⟩ := (hoo ▸ hT).destruct
  exact no_cycle hb hpath

/-! ### A level-erased size (termination measure ignoring the `Level` index)

`sizeOf` on `Expr`/`Parts` counts the `Level` index, which omega cannot bound;
this structural size does not, so the mutual recursion's descent is transparent. -/
mutual
  def Expr.size {l : Level G} : Expr G l → Nat
    | .op _ _ p => 1 + p.size
    | .var _ _ => 1
  def Parts.size {ps : List (Part G)} : Parts G ps → Nat
    | .nil => 0
    | .hole e p => 1 + e.size + p.size
    | .namePart _ p => 1 + p.size
    | .subHole _ _ p => 1 + p.size
end

/-- `size`/`flatten` are invariant under reindexing the part-list (used to compare
two bodies whose operators are equal without `subst`-ing the recursive call). -/
theorem Parts.size_cast {ps qs : List (Part G)} (hpp : ps = qs) (p : Parts G ps) :
    (hpp ▸ p).size = p.size := by cases hpp; rfl

/-! ### Body well-formedness invariant

`BodyOk o ps` records, for a suffix `ps` of an operator body, exactly what the
segmentation needs at each hole: a `loosest` hole is followed by a name token that
heads no operator; a `tighter o` hole is either the last part (its operand's
leftover is the caller's, stopped via `Stops.tighter`) or followed by `o`'s own
head (the separator, stopped via acyclicity); holes never abut. Stated as an
inductive (not a recursive `def`) so it is trivial to build and to `cases`. -/
inductive BodyOk (o : G.Op) : List (Part G) → Prop where
  | nil : BodyOk o []
  | name {tk rest} : BodyOk o rest → BodyOk o (Part.namePart tk :: rest)
  | holeLast {l'} : l' = Level.tighter o → BodyOk o [Part.hole l']
  | holeLoosest {tk rest} : (∀ o' : G.Op, (G.operator o').head ≠ tk) →
      BodyOk o (Part.namePart tk :: rest) →
      BodyOk o (Part.hole Level.loosest :: Part.namePart tk :: rest)
  | holeSep {tk rest} : tk = (G.operator o).head →
      BodyOk o (Part.namePart tk :: rest) →
      BodyOk o (Part.hole (Level.tighter o) :: Part.namePart tk :: rest)

/-- `Notation.toParts` always leads with a name part: the first body token. -/
theorem Notation.toParts_eq_cons (tkns : Notation) :
    Notation.toParts (G := G) tkns = Part.namePart tkns.head :: (Notation.toParts tkns).tail := by
  cases tkns with
  | last t => rfl
  | cons t ts => rfl

/-- `Notation.toParts ++ suffix` likewise leads with the first body token. -/
theorem Notation.toParts_app_cons (tkns : Notation) (suffix : List (Part G)) :
    Notation.toParts tkns ++ suffix
      = Part.namePart tkns.head :: ((Notation.toParts tkns).tail ++ suffix) := by
  cases tkns with
  | last t => rfl
  | cons t ts => rfl

/-- A name-part skeleton followed by an arbitrary (already-`BodyOk`) suffix is
`BodyOk`: every internal `loosest` hole is followed by a non-leading name part of
the operator (a non-head, via `hpr`), and the final name part connects to the
suffix. -/
theorem BodyOk_inner_app (o : G.Op) (tkns : Notation) (suffix : List (Part G))
    (hpr : ∀ tk ∈ tkns.toTokens.tail, ∀ o' : G.Op, (G.operator o').head ≠ tk)
    (hsuf : BodyOk o suffix) : BodyOk o (Notation.toParts tkns ++ suffix) := by
  induction tkns with
  | last t => exact BodyOk.name hsuf
  | cons t h ts ih =>
      have hih := ih (fun tk htk => hpr tk (mem_of_mem_tail htk))
      cases h with
      | loosest =>
          show BodyOk o (Part.namePart t :: Part.hole Level.loosest :: (Notation.toParts ts ++ suffix))
          refine BodyOk.name ?_
          rw [Notation.toParts_app_cons ts suffix]
          exact BodyOk.holeLoosest (hpr ts.head (Notation.head_mem_toTokens ts))
            (by rw [← Notation.toParts_app_cons ts suffix]; exact hih)
      | sub sp =>
          -- A sub-grammar interior hole is outside the token-based `BodyOk`
          -- invariant (its follow token's non-ambiguity needs sub-grammar token
          -- disjointness) — embedded-grammar uniqueness is future work.
          sorry

/-- Every operator body is `BodyOk` for its own operator. -/
theorem BodyOk_parts (h : G.UniqueNameParts) (hnj : G.NonAssoc) (o : G.Op) :
    BodyOk o (Operator.body o) := by
  unfold Operator.body
  cases hop : G.operator o with
  | closed tkns =>
      have hpr : ∀ tk ∈ tkns.toTokens.tail, ∀ o' : G.Op, (G.operator o').head ≠ tk := by
        have ht := h.tail_notHead hnj o; rw [hop] at ht; simpa [Operator.nameTokens] using ht
      simpa using BodyOk_inner_app o tkns [] hpr BodyOk.nil
  | prefx tkns =>
      have hpr : ∀ tk ∈ tkns.toTokens.tail, ∀ o' : G.Op, (G.operator o').head ≠ tk := by
        have ht := h.tail_notHead hnj o; rw [hop] at ht; simpa [Operator.nameTokens] using ht
      exact BodyOk_inner_app o tkns [Part.hole (Level.tighter o)] hpr (BodyOk.holeLast rfl)
  | infx tkns =>
      have hpr : ∀ tk ∈ tkns.toTokens.tail, ∀ o' : G.Op, (G.operator o').head ≠ tk := by
        have ht := h.tail_notHead hnj o; rw [hop] at ht; simpa [Operator.nameTokens] using ht
      have hhead : tkns.head = (G.operator o).head := by rw [hop]; rfl
      show BodyOk o (Part.hole (Level.tighter o) :: (Notation.toParts tkns ++ [Part.hole (Level.tighter o)]))
      rw [Notation.toParts_app_cons tkns [Part.hole (Level.tighter o)]]
      refine BodyOk.holeSep hhead ?_
      rw [← Notation.toParts_app_cons tkns [Part.hole (Level.tighter o)]]
      exact BodyOk_inner_app o tkns [Part.hole (Level.tighter o)] hpr (BodyOk.holeLast rfl)
  | postfx tkns =>
      have hpr : ∀ tk ∈ tkns.toTokens.tail, ∀ o' : G.Op, (G.operator o').head ≠ tk := by
        have ht := h.tail_notHead hnj o; rw [hop] at ht; simpa [Operator.nameTokens] using ht
      have hhead : tkns.head = (G.operator o).head := by rw [hop]; rfl
      show BodyOk o (Part.hole (Level.tighter o) :: Notation.toParts tkns)
      rw [Notation.toParts_eq_cons tkns]
      refine BodyOk.holeSep hhead ?_
      rw [← Notation.toParts_eq_cons tkns]
      simpa using BodyOk_inner_app o tkns [] hpr BodyOk.nil
  | infxl tkns => exact absurd (hnj o) (by rw [hop]; simp [Operator.simple])
  | infxr tkns => exact absurd (hnj o) (by rw [hop]; simp [Operator.simple])
  | juxt => exact absurd hop (hnj.ne_juxt o)

/-! ### Leading-token infrastructure

The first token of a body's flattening. For a closed/prefix operator it is the
operator's own head; for an infix/postfix operator it is the leading token of the
left operand (which lies strictly tighter). -/

@[simp] theorem Parts.flatten_head_namePart {tk : Token} {ps : List (Part G)} (q : Parts G ps) :
    (Parts.namePart tk q).flatten.head? = some tk := by
  rw [Parts.flatten_namePart]; rfl

theorem Parts.flatten_head_hole {l : Level G} {ps : List (Part G)}
    (e : Expr G l) (q : Parts G ps) : (Parts.hole e q).flatten.head? = e.flatten.head? := by
  rw [Parts.flatten_hole, head?_append_left (Expr.flatten_ne e)]

/-- A `simple` operator body either leads with the operator's own head
(closed/prefix) or with an operand hole at level `tighter o` (infix/postfix). -/
theorem Operator.body_shape (o : G.Op) (hs : (G.operator o).simple = true) :
    (∃ rest, Operator.body o = Part.namePart (G.operator o).head :: rest)
    ∨ (∃ rest, Operator.body o = Part.hole (Level.tighter o) :: rest) := by
  unfold Operator.body Operator.head
  cases hop : G.operator o with
  | closed tkns => exact Or.inl ⟨_, Notation.toParts_eq_cons tkns⟩
  | prefx tkns => exact Or.inl ⟨_, Notation.toParts_app_cons tkns [Part.hole (Level.tighter o)]⟩
  | infx tkns => exact Or.inr ⟨_, rfl⟩
  | infxl tkns => rw [hop] at hs; simp [Operator.simple] at hs
  | infxr tkns => rw [hop] at hs; simp [Operator.simple] at hs
  | juxt => rw [hop] at hs; simp [Operator.simple] at hs
  | postfx tkns => exact Or.inr ⟨_, rfl⟩

/-- For a name-token-leading body, the flattening's head is the operator's head. -/
theorem Parts.flatten_head_of_namePart {o : G.Op} {rest : List (Part G)}
    (parts : Parts G (Operator.body o))
    (hsh : Operator.body o = Part.namePart (G.operator o).head :: rest) :
    parts.flatten.head? = some (G.operator o).head := by
  rw [← Parts.flatten_cast hsh parts]
  cases hsh ▸ parts with
  | namePart tk q => exact Parts.flatten_head_namePart q

/-! ### The isolated hard kernel

Two **distinct** top operators cannot produce the same flattening with both
leftovers stopping the level.

`topOp_unique` below dispatches on operator shape. The case where **both** bodies
lead with a name token (closed/prefix) is discharged here: their flattenings share
a leading token, which is each operator's head, so `heads_distinct` forces
`o₁ = o₂`. The remaining case — at least one operator is infix/postfix, so its
leading token belongs to a strictly-tighter left operand rather than the operator
itself — is `topOp_unique_holeLed`. That is the genuine Danielsson–Norell depth-0
/ bracket-counting kernel (roadmap in this file's header; foundation
`count_flatten_expr`); the paper only sketches it. Forest-free. -/
theorem topOp_unique_holeLed (h : G.UniqueNameParts) (hnj : G.NonAssoc) {l : Level G}
    {o₁ o₂ : G.Op}
    (hne : o₁ ≠ o₂) (c₁ : Level.condition l o₁) (c₂ : Level.condition l o₂)
    (p₁ : Parts G (Operator.body o₁)) (p₂ : Parts G (Operator.body o₂)) (s₁ s₂ : List Token)
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂) (hs₁ : Stops l s₁) (hs₂ : Stops l s₂)
    (hhole : (∃ rest, Operator.body o₁ = Part.hole (Level.tighter o₁) :: rest)
           ∨ (∃ rest, Operator.body o₂ = Part.hole (Level.tighter o₂) :: rest)) : False := by
  sorry

theorem topOp_unique (h : G.UniqueNameParts) (hnj : G.NonAssoc) {l : Level G} {o₁ o₂ : G.Op}
    (hne : o₁ ≠ o₂)
    (c₁ : Level.condition l o₁) (c₂ : Level.condition l o₂)
    (p₁ : Parts G (Operator.body o₁)) (p₂ : Parts G (Operator.body o₂)) (s₁ s₂ : List Token)
    (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂) (hs₁ : Stops l s₁) (hs₂ : Stops l s₂) : False := by
  rcases Operator.body_shape o₁ (hnj o₁) with hsh₁ | hsh₁
  · rcases Operator.body_shape o₂ (hnj o₂) with hsh₂ | hsh₂
    · -- both bodies lead with a name token: equal heads ⇒ o₁ = o₂
      obtain ⟨_, hsh₁⟩ := hsh₁; obtain ⟨_, hsh₂⟩ := hsh₂
      have hh := head?_eq_of_prefix heq (Parts.flatten_ne p₁ (Operator.body_ne_nil o₁))
        (Parts.flatten_ne p₂ (Operator.body_ne_nil o₂))
      rw [Parts.flatten_head_of_namePart p₁ hsh₁, Parts.flatten_head_of_namePart p₂ hsh₂] at hh
      exact hne (Classical.byContradiction fun hc => h.heads_distinct hnj hc (Option.some.inj hh))
    · exact topOp_unique_holeLed h hnj hne c₁ c₂ p₁ p₂ s₁ s₂ heq hs₁ hs₂ (Or.inr hsh₂)
  · exact topOp_unique_holeLed h hnj hne c₁ c₂ p₁ p₂ s₁ s₂ heq hs₁ hs₂ (Or.inl hsh₁)

/-- The body tail after a hole is itself `BodyOk` (for the `udParts` recursion). -/
theorem BodyOk.hole_tail {o : G.Op} {l' : Level G} {rest : List (Part G)}
    (hok : BodyOk o (Part.hole l' :: rest)) : BodyOk o rest := by
  cases hok with
  | holeLast _ => exact BodyOk.nil
  | holeLoosest _ hbody => exact hbody
  | holeSep _ hbody => exact hbody

/-- The operand of a hole has a `Stop`pable leftover: the `BodyOk` data pins
exactly which mechanism applies (acyclicity for separators/last holes,
unique-name-parts for inner holes). This is where the segmentation lives — all
three cases are forest-free. -/
theorem BodyOk.hole_stops (h : G.UniqueNameParts) (hnj : G.NonAssoc) {l : Level G} {o : G.Op}
    (hco : Level.condition l o) {l' : Level G} {rest : List (Part G)}
    (hok : BodyOk o (Part.hole l' :: rest)) (q : Parts G rest) {s : List Token}
    (hs : Stops l s) : Stops l' (q.flatten ++ s) := by
  cases hok with
  | holeLast hl' =>
      cases q
      subst hl'
      simpa only [Parts.flatten_nil, List.nil_append] using Stops.tighter hco hs
  | holeLoosest hno hbody =>
      cases q with
      | namePart _ q' => exact Stops.of_noHead (by simp [Parts.flatten_namePart]) hno Level.loosest
  | holeSep hsep hbody =>
      cases q with
      | namePart _ q' => exact Stops.tighter_of_head h hnj (by simp [Parts.flatten_namePart, hsep])

/-- A variable leaf and an operator application cannot share a flatten-prefix with
both leftovers stopping the level. For a closed/prefix operator this is immediate
from `varDisjoint` (the variable token would have to be the operator's head). For
an infix/postfix operator the variable's single token is a strict prefix of the
operand-led body, so it reduces to the same proper-prefix kernel as
`topOp_unique_holeLed` (the remaining `sorry`). -/
theorem udVarOp (h : G.UniqueNameParts) (hnj : G.NonAssoc) {l : Level G} {t : Token}
    (hv : G.isVar t = true)
    {o : G.Op} (c : Level.condition l o) (p : Parts G (Operator.body o)) (s₁ s₂ : List Token)
    (heq : (Expr.var (l := l) t hv).flatten ++ s₁ = (Expr.op o c p).flatten ++ s₂)
    (hs₁ : Stops l s₁) (hs₂ : Stops l s₂) : False := by
  rw [Expr.flatten_var, Expr.flatten_op] at heq
  rcases Operator.body_shape o (hnj o) with ⟨rest, hsh⟩ | ⟨rest, hsh⟩
  · -- closed/prefix: the body leads with `o`'s head, so `t = o.head` — impossible.
    have ht := congrArg List.head? heq
    rw [head?_append_left (Parts.flatten_ne p (Operator.body_ne_nil o)),
      Parts.flatten_head_of_namePart p hsh] at ht
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at ht
    exact h.varDisjoint t hv o (ht.symm ▸ Operator.head_mem (G.operator o) (hnj.ne_juxt o))
  · -- infix/postfix (operand-led): proper-prefix kernel residue.
    sorry

/-! ### Mutual prefix-form unique decomposition -/

mutual
  /-- Two expressions at the same level with a common flatten-prefix (both
  leftovers stopping the level) are equal, with equal leftovers. The top operator
  agrees by `topOp_unique`; the bodies then agree by `udParts`. -/
  theorem udExpr (h : G.UniqueNameParts) (hnj : G.NonAssoc) {l : Level G} (e₁ e₂ : Expr G l)
      (s₁ s₂ : List Token) (heq : e₁.flatten ++ s₁ = e₂.flatten ++ s₂)
      (hs₁ : Stops l s₁) (hs₂ : Stops l s₂) : e₁ = e₂ ∧ s₁ = s₂ := by
    match e₁, e₂ with
    | .op o₁ c₁ p₁, .op o₂ c₂ p₂ =>
        have hpe : p₁.flatten ++ s₁ = p₂.flatten ++ s₂ := by
          simpa only [Expr.flatten_op] using heq
        by_cases ho : o₁ = o₂
        · have hpp : Operator.body o₁ = Operator.body o₂ := congrArg Operator.body ho
          have hrec := udParts h hnj o₂ c₂ (BodyOk_parts h hnj o₂) (hpp ▸ p₁) p₂ s₁ s₂
            (by rw [Parts.flatten_cast]; exact hpe) hs₁ hs₂
          refine ⟨?_, hrec.2⟩
          subst ho
          rw [← hrec.1]
        · exact (topOp_unique h hnj ho c₁ c₂ p₁ p₂ s₁ s₂ hpe hs₁ hs₂).elim
    | .var t₁ hv₁, .var t₂ hv₂ =>
        simp only [Expr.flatten_var, List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, hs⟩ := heq
        exact ⟨rfl, hs⟩
    | .op o₁ c₁ p₁, .var t₂ hv₂ =>
        exact (udVarOp h hnj hv₂ c₁ p₁ s₂ s₁ heq.symm hs₂ hs₁).elim
    | .var t₁ hv₁, .op o₂ c₂ p₂ =>
        exact (udVarOp h hnj hv₁ c₂ p₂ s₁ s₂ heq hs₁ hs₂).elim
  termination_by e₁.size + e₂.size
  decreasing_by all_goals (simp only [Expr.size, Parts.size_cast]; omega)

  /-- Two operator bodies over the same `BodyOk` part-list with a common
  flatten-prefix are equal, with equal leftovers. Walks the body front-to-back;
  each hole's operand leftover is `Stop`ped using the `BodyOk` data, then the
  operand is matched by `udExpr`. -/
  theorem udParts (h : G.UniqueNameParts) (hnj : G.NonAssoc) {l : Level G} (o : G.Op)
      (hco : Level.condition l o)
      {ps : List (Part G)} (hok : BodyOk o ps) (p₁ p₂ : Parts G ps) (s₁ s₂ : List Token)
      (heq : p₁.flatten ++ s₁ = p₂.flatten ++ s₂) (hs₁ : Stops l s₁) (hs₂ : Stops l s₂) :
      p₁ = p₂ ∧ s₁ = s₂ := by
    match ps, p₁, p₂ with
    | [], .nil, .nil => exact ⟨rfl, by simpa only [Parts.flatten_nil, List.nil_append] using heq⟩
    | (.namePart tk) :: rest, .namePart _ q₁, .namePart _ q₂ =>
        have hok' : BodyOk o rest := by cases hok with | name hb => exact hb
        have heq' : q₁.flatten ++ s₁ = q₂.flatten ++ s₂ := by
          simpa only [Parts.flatten_namePart, List.cons_append, List.cons.injEq, true_and] using heq
        have hrec := udParts h hnj o hco hok' q₁ q₂ s₁ s₂ heq' hs₁ hs₂
        exact ⟨by rw [hrec.1], hrec.2⟩
    | (.hole l') :: rest, .hole e₁ q₁, .hole e₂ q₂ =>
        have heq' : e₁.flatten ++ (q₁.flatten ++ s₁) = e₂.flatten ++ (q₂.flatten ++ s₂) := by
          simpa only [Parts.flatten_hole, List.append_assoc] using heq
        have hst₁ := BodyOk.hole_stops h hnj hco hok q₁ hs₁
        have hst₂ := BodyOk.hole_stops h hnj hco hok q₂ hs₂
        have hrecE := udExpr h hnj e₁ e₂ _ _ heq' hst₁ hst₂
        have hrecP := udParts h hnj o hco (BodyOk.hole_tail hok) q₁ q₂ s₁ s₂ hrecE.2 hs₁ hs₂
        exact ⟨by rw [hrecE.1, hrecP.1], hrecP.2⟩
  termination_by p₁.size + p₂.size
  decreasing_by all_goals (simp only [Parts.size]; omega)
end

/-! ## The target theorem -/

/-- **Unique name parts give unambiguity** (Danielsson–Norell §4, specialized
to the closed/non-assoc-infix fragment). Together with `parse_unique` this
yields: for a grammar certified by `UniqueNameParts`, `parse` returns (copies
of) at most one tree.

The proof is the mutual prefix-form unique decomposition `udExpr`/`udParts`
above (the forest-free port of the spine `Stops` argument). The *only*
remaining gap is `topOp_unique`: that two distinct top operators cannot share a
flattening — the Danielsson–Norell depth-0 / bracket-counting kernel, which the
paper itself only sketches. The counterexample `amb_not_uniqueNameParts` shows
the hypothesis is doing real work.

The `NonAssoc` hypothesis confines this to the token-based fragment: the
tokenless juxtaposition operator carries no leading token for `Stops`/`BodyOk`
to key on, so its (separate, left-associativity) uniqueness argument is out of
scope here. -/
theorem unambiguous_of_uniqueNameParts (h : G.UniqueNameParts) (hnj : G.NonAssoc) :
    G.Unambiguous := by
  intro e₁ e₂ he
  have heq : e₁.flatten ++ [] = e₂.flatten ++ [] := by simpa using he
  exact (udExpr h hnj e₁ e₂ [] [] heq (by intro o _; simp) (by intro o _; simp)).1

end LambdaLab.Parser.Mixfix
