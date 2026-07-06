import LambdaLab.ParserOld.Mixfix.Verified

/-!
# Interpreting parse trees into a carrier family (`Interp`)

The forward half of truncation, standalone and law-free. An `Interp` assigns:

* a carrier type `eInt e` to each entry `e`,
* an interpretation of every operator (a combinator of the operator's `shape`),
* an interpretation of variable leaves.

`Expr.truncate` then folds it over a parse tree, producing the carrier value.
-/

namespace LambdaLab.ParserOld.Mixfix

/-- The interior holes of a notation, as curried argument types in front of a
`Tail` type. A hole `cons _ e' _` references entry `e'`, so it contributes that
entry's carrier `eInt e'` as an argument. -/
def Notation.shapeArgs {G : Grammar} (eInt : G.Ent → Type u) :
    Notation G.Ent → Type u → Type u
  | .last _,         Tail => Tail
  | .cons _ e' rest, Tail => eInt e' → Notation.shapeArgs eInt rest Tail

/-- The **shape** of an operator of host entry `e`: the type of a combinator that
takes each operand and returns the host carrier `eInt e`. Interior notation holes
contribute the referenced entry's carrier `eInt e'`; the fixity's leading/trailing
operands reference the host entry, so they contribute `eInt e`.

* `closed`  `( _ )`               → `eInt e`
* `prefx`   `op _`                → `eInt e → eInt e`
* `infx`/`infxl`/`infxr` `_ op _` → `eInt e → … → eInt e → eInt e`
* `postfx`  `_ op`                → `eInt e → eInt e`
* `juxt`    `_ _`                 → `eInt e → eInt e → eInt e` -/
def Operator.shape {G : Grammar} (eInt : G.Ent → Type u) (e : G.Ent) :
    Operator G.Ent → Type u
  | .closed n => Notation.shapeArgs eInt n (eInt e)
  | .prefx n  => Notation.shapeArgs eInt n (eInt e → eInt e)
  | .infx n   => eInt e → Notation.shapeArgs eInt n (eInt e → eInt e)
  | .infxl n  => eInt e → Notation.shapeArgs eInt n (eInt e → eInt e)
  | .infxr n  => eInt e → Notation.shapeArgs eInt n (eInt e → eInt e)
  | .postfx n => eInt e → Notation.shapeArgs eInt n (eInt e)
  | .juxt     => eInt e → eInt e → eInt e

/-- A grammar **interpretation**: a carrier per entry, an operator combinator of
the right `shape` for each operator, and a variable map. No laws — this is exactly
the data that a fold over parse trees consumes. -/
structure Interp (G : Grammar) where
  eInt : G.Ent → Type
  oInt : (e : G.Ent) → (o : (G.entry e).Op) →
    Operator.shape eInt e ((G.entry e).operator o)
  vInt : (e : G.Ent) → Token → eInt e

/-! ## Folding an interpretation over a parse tree

`truncate` walks an `Expr`, applying `oInt` at each operator node and `vInt` at
each variable leaf. To apply an operator's curried combinator to the (already
interpreted) hole values, we retype it via `shape_eq_partsFun`: the operator's
`shape` is exactly the "consume the body's holes, return `eInt e`" type. -/

/-- The curried argument type of a combinator that consumes the **holes** of a
parts list (name tokens contribute nothing) and returns `R`. -/
def partsFun {G : Grammar} (eInt : G.Ent → Type) (R : Type) : List (Part G) → Type
  | [] => R
  | .namePart _ :: rest => partsFun eInt R rest
  | .hole e' _ :: rest => eInt e' → partsFun eInt R rest

theorem partsFun_append {G : Grammar} (eInt : G.Ent → Type) (R : Type)
    (xs ys : List (Part G)) :
    partsFun eInt R (xs ++ ys) = partsFun eInt (partsFun eInt R ys) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [partsFun, ih]

theorem shapeArgs_eq_partsFun {G : Grammar} (eInt : G.Ent → Type) (Tail : Type)
    (n : Notation G.Ent) :
    Notation.shapeArgs eInt n Tail = partsFun eInt Tail (Notation.toParts n) := by
  induction n with
  | last tkn => rfl
  | cons tkn e' rest ih => simp [Notation.shapeArgs, Notation.toParts, partsFun, ih]

/-- An operator's `shape` **is** the hole-argument type of its body — so its
combinator can be applied directly to the holes of a `Parts G (Operator.body e o)`. -/
theorem shape_eq_partsFun {G : Grammar} (eInt : G.Ent → Type) (e : G.Ent)
    (o : (G.entry e).Op) :
    Operator.shape eInt e ((G.entry e).operator o)
      = partsFun eInt (eInt e) (Operator.body e o) := by
  unfold Operator.body
  cases (G.entry e).operator o with
  | closed n => simp [Operator.shape, shapeArgs_eq_partsFun]
  | juxt => simp [Operator.shape, partsFun]
  | prefx n | infx n | infxl n | infxr n | postfx n =>
      simp [Operator.shape, partsFun_append, shapeArgs_eq_partsFun, partsFun]

mutual
  /-- Interpret a parse tree of any level into its carrier value, folding `oInt` at
  operator nodes and `vInt` at variable leaves. The carrier does not depend on the
  level, so the fold is uniform across all levels. -/
  def Expr.truncate {G : Grammar} (i : Interp G) {e : G.Ent}
      {l : Level (G.entry e)} (expr : Expr G e l) : i.eInt e :=
    match expr with
    | .op o _ parts =>
        Parts.truncateApply i (Operator.body e o) (shape_eq_partsFun i.eInt e o ▸ i.oInt e o) parts
    | .var x _ => i.vInt e x
  termination_by sizeOf expr

  /-- Apply a curried combinator (typed by `partsFun`) to the interpreted holes of
  a parts list, skipping name tokens. -/
  def Parts.truncateApply {G : Grammar} (i : Interp G) {R : Type}
      (ps : List (Part G)) (f : partsFun i.eInt R ps) (parts : Parts G ps) : R :=
    match ps, f, parts with
    | _, f, .nil => f
    | .namePart _ :: ps', f, .namePart _ rest => Parts.truncateApply i ps' f rest
    | .hole _ _ :: ps', f, .hole ex rest =>
        Parts.truncateApply i ps' (f (Expr.truncate i ex)) rest
  termination_by sizeOf parts
end

/-- A tuple of hole values for `ps`, each **strictly smaller** than `bound` under
`size` (name tokens contribute nothing). The size-bounded `partsVal` — that bound
is exactly the decrease witness that makes the derived `lift` terminate. -/
def smallVals {G : Grammar} (eInt : G.Ent → Type) (size : (e : G.Ent) → eInt e → Nat)
    (bound : Nat) : List (Part G) → Type
  | [] => PUnit
  | .namePart _ :: rest => smallVals eInt size bound rest
  | .hole e' _ :: rest => { w : eInt e' // size e' w < bound } × smallVals eInt size bound rest

/-- Apply a curried combinator (typed by `partsFun`) to a tuple of **carrier
values** (the `eInt` carried in `smallVals`), skipping name tokens. The
value-analogue of `Parts.truncateApply`; used to state `view_build`. -/
def applyVals {G : Grammar} (eInt : G.Ent → Type) (size : (e : G.Ent) → eInt e → Nat)
    {R : Type} (bound : Nat) :
    (ps : List (Part G)) → partsFun eInt R ps → smallVals eInt size bound ps → R
  | [],                  f, _        => f
  | .namePart _ :: ps',  f, vs       => applyVals eInt size bound ps' f vs
  | .hole _ _ :: ps',    f, ⟨sub, vs⟩ => applyVals eInt size bound ps' (f sub.1) vs

structure ReverseInterp (G : Grammar) extends Interp G where
  /-- A well-founded measure on carrier values, strictly shrunk by `view` — what
  makes the inverse `lift` terminate. -/
  size : (e : G.Ent) → eInt e → Nat
  /-- One-layer **view** of a carrier value: either a variable leaf (a valid
  token), or a **loosest** operator `o` together with its holes as
  (not-yet-reversed) carrier values — each strictly smaller than `size v`, so
  `lift` descends. -/
  view : (e : G.Ent) → (v : eInt e) →
    { t : Token // (G.entry e).isVar t = true } ⊕
      Σ o : { o : (G.entry e).Op // Level.condition Level.loosest o },
        smallVals eInt size (size e v) (Operator.body e o.1)
  /-- A user-supplied decision procedure for `Level.condition l o` — does operator
  `o` sit at level `l`? Being `Decidable`, it carries its own correctness (no extra
  law), and can beat searching the `tighter` graph. Placement uses it to
  parenthesize only when precedence forces it. -/
  decLevel : {e : G.Ent} → (l : Level (G.entry e)) → (o : (G.entry e).Op) →
    Decidable (Level.condition l o)
  /-- Place a full (loosest) operand into the level a hole demands, adding
  parentheses only when precedence forces it (loosening never needs any). -/
  wrap : {e : G.Ent} → (l : Level (G.entry e)) → Expr G e .loosest → Expr G e l
  /-- **Law** — parentheses are invisible to the semantics: `wrap`ping an operand
  and then interpreting it agrees with interpreting it directly. This is what makes
  `place` transparent to `truncate`. -/
  wrap_truncate : ∀ {e : G.Ent} (l : Level (G.entry e)) (x : Expr G e .loosest),
    Expr.truncate toInterp (wrap l x) = Expr.truncate toInterp x
  /-- **Law** — `view` inverts the constructor: re-interpreting the pieces it hands
  back (`vInt` on a variable token, `oInt` applied to the hole *values* on an
  operator) rebuilds the original `v`. -/
  view_build : ∀ {e : G.Ent} (v : eInt e),
    (match view e v with
     | .inl ⟨tk, _⟩        => vInt e tk
     | .inr ⟨⟨o, _⟩, vals⟩ =>
         applyVals eInt size (size e v) (Operator.body e o)
           (shape_eq_partsFun eInt e o ▸ oInt e o) vals) = v

/-- Place a reversed (loosest) operand into the level a hole demands, with
**minimal** parentheses: a variable fits every level; an operator that already
fits `l` (by `decLevel`) is reindexed as-is; only an operator that does *not* fit
is `wrap`ped. So `wrap` fires exactly when precedence forces parentheses. -/
def ReverseInterp.place {G : Grammar} (t : ReverseInterp G) {e : G.Ent}
    (l : Level (G.entry e)) (sub : Expr G e .loosest) : Expr G e l :=
  match sub with
  | .var tok h     => .var tok h
  | .op o hc parts =>
      match t.decLevel l o with
      | isTrue cond => .op o cond parts
      | isFalse _   => t.wrap l (.op o hc parts)

/-! ## The derived inverse `lift` (total, well-founded on `size`)

`lift` rebuilds a loosest parse tree from a carrier value: `view` recovers the
head, `liftBody` reverses each hole value (`lift` again) and `place`s it into the
level its hole demands. It terminates by the lexicographic measure
`(size v, phase, length)`: the middle "phase" bit orders a `lift` node above the
`liftBody` that serves it, and the `size` decrease comes from `view`'s `smallVals`
bound. -/
mutual
  /-- Rebuild a loosest parse tree from a carrier value (the inverse of
  `truncate`). -/
  def ReverseInterp.lift {G : Grammar} (t : ReverseInterp G) (e : G.Ent)
      (v : t.eInt e) : Expr G e .loosest :=
    match t.view e v with
    | .inl ⟨tok, h⟩          => Expr.var tok h
    | .inr ⟨⟨o, cond⟩, vals⟩ =>
        Expr.op o cond (t.liftBody (t.size e v) (Operator.body e o) vals)
  termination_by (t.size e v, 1, 0)
  decreasing_by exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  /-- Assemble an operator body: reverse each hole value with `lift`, `place` it
  into the level the hole demands, and thread the name tokens through. -/
  def ReverseInterp.liftBody {G : Grammar} (t : ReverseInterp G) (bound : Nat)
      (ps : List (Part G)) (vs : smallVals t.eInt t.size bound ps) : Parts G ps :=
    match ps, vs with
    | [],                   _              => .nil
    | .namePart tk :: rest, vs             => .namePart tk (t.liftBody bound rest vs)
    | .hole e' l' :: rest,  (sub, vs) => .hole (t.place l' (t.lift e' sub.1)) (t.liftBody bound rest vs)
  termination_by (bound, 0, ps.length)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ sub.2
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp only [List.length_cons]; omega))
end

/-! ## Round-trip: `truncate ∘ lift = id`

The two laws (`wrap_truncate`, `view_build`) plus the `size` discipline in `view`'s
type suffice: reversing a carrier value and re-interpreting it returns the value.
`size` needs no law — its decrease lives in `view`'s `smallVals` bound. -/

/-- `place` is invisible to `truncate`: a variable is placed verbatim; an operator
that already fits is only reindexed (and `truncate` ignores the level proof); an
operator that is `wrap`ped vanishes by `wrap_truncate`. -/
theorem ReverseInterp.place_truncate {G : Grammar} (t : ReverseInterp G) {e : G.Ent}
    (l : Level (G.entry e)) (sub : Expr G e .loosest) :
    Expr.truncate t.toInterp (t.place l sub) = Expr.truncate t.toInterp sub := by
  cases sub with
  | var tok h => simp only [ReverseInterp.place, Expr.truncate]
  | op o hc parts =>
      simp only [ReverseInterp.place]
      split
      · simp only [Expr.truncate]
      · exact t.wrap_truncate l _

/-- Body-level step: interpreting a `liftBody`-assembled body equals applying the
combinator straight to the (round-tripped) hole values — given each hole value
round-trips (`ih`). Each operand's `place` vanishes by `place_truncate`, then `ih`
collapses `truncate (lift w)` back to `w`. -/
theorem truncateApply_liftBody {G : Grammar} (t : ReverseInterp G) (bound : Nat)
    (ih : ∀ {e' : G.Ent} (w : t.eInt e'), t.size e' w < bound →
          Expr.truncate t.toInterp (t.lift e' w) = w)
    {R : Type} (ps : List (Part G)) (f : partsFun t.eInt R ps)
    (vs : smallVals t.eInt t.size bound ps) :
    Parts.truncateApply t.toInterp ps f (t.liftBody bound ps vs)
      = applyVals t.eInt t.size bound ps f vs := by
  induction ps with
  | nil => simp only [ReverseInterp.liftBody, Parts.truncateApply, applyVals]
  | cons p ps' ihp =>
      cases p with
      | namePart tk =>
          simp only [ReverseInterp.liftBody, Parts.truncateApply, applyVals]
          exact ihp f vs
      | hole e' l' =>
          obtain ⟨sub, vs'⟩ := vs
          simp only [ReverseInterp.liftBody, Parts.truncateApply, applyVals]
          rw [t.place_truncate, ih sub.1 sub.2]
          exact ihp (f sub.1) vs'

/-- **Round-trip**: reversing a carrier value and re-interpreting it returns the
value. Strong induction on `size`: the variable case is `view_build`; the operator
case strips each operand's `place` and round-trips the smaller hole values
(`truncateApply_liftBody` with the IH), then reassembles `v` (`view_build`). -/
theorem ReverseInterp.truncate_lift {G : Grammar} (t : ReverseInterp G) {e : G.Ent}
    (v : t.eInt e) : Expr.truncate t.toInterp (t.lift e v) = v := by
  suffices H : ∀ n, ∀ {e : G.Ent} (v : t.eInt e), t.size e v < n →
      Expr.truncate t.toInterp (t.lift e v) = v from H _ v (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun v h => absurd h (Nat.not_lt_zero _)
  | succ n IH =>
      intro e v h
      have hvb := t.view_build v
      rw [ReverseInterp.lift]
      rcases hv : t.view e v with ⟨tok, htok⟩ | ⟨⟨o, cond⟩, vals⟩
      · simp only [hv] at hvb
        simpa only [Expr.truncate] using hvb
      · simp only [hv] at hvb
        simp only [Expr.truncate]
        rw [truncateApply_liftBody t (t.size e v) (fun {e'} w hw => IH w (by omega))]
        exact hvb

/-! ## Packaging as a `TruncatingParser`

A `ReverseInterp` at a chosen start entry is exactly a `TruncatingParser`: the
grammar's precedence parser supplies `parse` (each tree `truncate`d to a carrier
value), and `lift` + `flatten` supply the canonical `render`. -/

/-- Bundle a `ReverseInterp` at start entry `e` as a `TruncatingParser`:

* `parse` — run the grammar's precedence parser and `truncate` every tree to a
  carrier value (keeping each leftover);
* `render` — `lift` a value back to a minimally-parenthesized tree and `flatten` it.

The print→parse round-trip is immediate from `truncate_lift`: `render b` parses
back (via `parseExpr_complete`) to `lift e b`, whose `truncate` is `b`. Because
`truncate_lift` holds for *every* carrier value, the "`b` was produced" hypothesis
is never used. -/
def ReverseInterp.toTruncatingParser {G : Grammar} (t : ReverseInterp G) (e : G.Ent) :
    TruncatingParser Token (t.eInt e) where
  parse tkns := (parseExpr e .loosest tkns).map (fun x => (Expr.truncate t.toInterp x.1, x.2))
  render v := (t.lift e v).flatten
  complete := by
    intro _input b _s _hmem rest
    obtain ⟨r, hr, hm⟩ :=
      parseExpr_complete (t.lift e b) ((t.lift e b).flatten ++ rest) rest rfl
    exact ⟨r, hr, List.mem_map.mpr ⟨(t.lift e b, r), hm, by rw [t.truncate_lift]⟩⟩

end LambdaLab.ParserOld.Mixfix
