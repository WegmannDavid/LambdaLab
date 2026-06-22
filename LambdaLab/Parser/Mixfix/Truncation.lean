import LambdaLab.Parser.Mixfix.Tree

namespace LambdaLab.Parser.Mixfix

/-- The interior holes of a notation, as curried argument types in front of a
`Tail` type. A notation hole `cons _ e' _` references entry `e'`, so it
contributes a `Base e'` argument — the carrier of that entry's sub-language
(recursive when `e'` is the host entry, cross-entry otherwise; both are the same
construct). -/
def Notation.shapeArgs {G : Grammar} (eInt : G.Ent → Type u) :
    Notation G.Ent → Type u → Type u
  | .last _,         Tail => Tail
  | .cons _ e' rest, Tail => eInt e' → Notation.shapeArgs eInt rest Tail

/-- The **shape** of an operator of host entry `e`: the type of a combinator
taking each operand and returning the host carrier `Base e`. Interior notation
holes contribute the referenced entry's carrier `eInt e'` (via `shapeArgs`); the
fixity's leading/trailing operands reference the host entry, so they contribute
`eInt e`. The arity is the notation's interior holes plus the fixity's
leading/trailing operands.

* `closed`  `( _ )`               → `eInt e`
* `prefx`   `op _`                → `eInt e → eInt e`
* `infx`/`infxl`/`infxr` `_ op _` → `eInt e → … → eInt e → eInt e`
* `postfx`  `_ op`                → `eInt e → eInt e`
* `juxt`    `_ _`                 → `eInt e → eInt e → eInt e`

Since holes are entry references (no embedded `Type`), there is no universe bump:
a single `u` carries every entry's carrier. -/
def Operator.shape {G : Grammar} (eInt : G.Ent → Type u) (e : G.Ent) :
    Operator G.Ent → Type u
  | .closed n => Notation.shapeArgs eInt n (eInt e)
  | .prefx n  => Notation.shapeArgs eInt n (eInt e → eInt e)
  | .infx n   => eInt e → Notation.shapeArgs eInt n (eInt e → eInt e)
  | .infxl n  => eInt e → Notation.shapeArgs eInt n (eInt e → eInt e)
  | .infxr n  => eInt e → Notation.shapeArgs eInt n (eInt e → eInt e)
  | .postfx n => eInt e → Notation.shapeArgs eInt n (eInt e)
  | .juxt     => eInt e → eInt e → eInt e

/-- A **truncation** of a grammar: a semantic interpretation of its parse trees.
Each entry `e` gets a carrier `eInt e`; every operator of `e` is interpreted as a
combinator of its `shape`, and every variable leaf maps into the carrier.

There is no sub-parser field: a cross-entry hole is just another entry,
interpreted by the *same* `eInt`/`interpretation` family — the old `subTruncation`
collapses into the family. -/
structure Truncation (G : Grammar) where
  eInt : G.Ent → Type
  oInt : (e : G.Ent) → (o : (G.entry e).Op) →
    Operator.shape eInt e ((G.entry e).operator o)
  vInt : (e : G.Ent) → Token → eInt e

/-! ## The forward map: `truncate`

`truncate` folds the interpretation over a parse tree, applying `oInt` at each
operator node and `vInt` at each variable leaf. The carrier `t.eInt e` does not
depend on the level, so the fold is uniform across *all* levels — only the entry
matters. -/

/-- The curried argument type of a combinator that consumes the **holes** of a
parts list (name tokens contribute nothing) and returns `R`. By construction
`partsFun t (t.eInt e) (Operator.body e o)` is the operator's `shape` — see
`shape_eq_partsFun`. -/
def partsFun {G : Grammar} (t : Truncation G) (R : Type) : List (Part G) → Type
  | [] => R
  | .namePart _ :: rest => partsFun t R rest
  | .hole e' _ :: rest => t.eInt e' → partsFun t R rest

theorem partsFun_append {G : Grammar} (t : Truncation G) (R : Type)
    (xs ys : List (Part G)) :
    partsFun t R (xs ++ ys) = partsFun t (partsFun t R ys) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [partsFun, ih]

theorem shapeArgs_eq_partsFun {G : Grammar} (t : Truncation G) (Tail : Type)
    (n : Notation G.Ent) :
    Notation.shapeArgs t.eInt n Tail = partsFun t Tail (Notation.toParts n) := by
  induction n with
  | last tkn => rfl
  | cons tkn e' rest ih => simp [Notation.shapeArgs, Notation.toParts, partsFun, ih]

/-- The operator's `shape` *is* the hole-argument type of its body — so the
combinator `t.oInt e o` can be applied directly to the truncated holes of a
`Parts G (Operator.body e o)`. -/
theorem shape_eq_partsFun {G : Grammar} (t : Truncation G) (e : G.Ent)
    (o : (G.entry e).Op) :
    Operator.shape t.eInt e ((G.entry e).operator o)
      = partsFun t (t.eInt e) (Operator.body e o) := by
  unfold Operator.body
  cases (G.entry e).operator o with
  | closed n => simp [Operator.shape, shapeArgs_eq_partsFun]
  | juxt => simp [Operator.shape, partsFun]
  | prefx n | infx n | infxl n | infxr n | postfx n =>
      simp [Operator.shape, partsFun_append, shapeArgs_eq_partsFun, partsFun]

mutual
  /-- Truncate a parse tree of any level to its semantic value. -/
  def Expr.truncate {G : Grammar} (t : Truncation G) {e : G.Ent}
      {l : Level (G.entry e)} (expr : Expr G e l) : t.eInt e :=
    match expr with
    | .op o _ parts =>
        Parts.truncateApply t (Operator.body e o) (shape_eq_partsFun t e o ▸ t.oInt e o) parts
    | .var x _ => t.vInt e x
  termination_by sizeOf expr

  /-- Apply a curried combinator (typed by `partsFun`) to the truncated holes of
  a parts list, skipping name tokens. -/
  def Parts.truncateApply {G : Grammar} (t : Truncation G) {R : Type}
      (ps : List (Part G)) (f : partsFun t R ps) (parts : Parts G ps) : R :=
    match ps, f, parts with
    | _, f, .nil => f
    | .namePart _ :: ps', f, .namePart _ rest => Parts.truncateApply t ps' f rest
    | .hole _ _ :: ps', f, .hole ex rest =>
        Parts.truncateApply t ps' (f (Expr.truncate t ex)) rest
  termination_by sizeOf parts
end

/-- Truncate a full (loosest) parse tree — the level-general `Expr.truncate`
specialized to the parser's output level. -/
def Truncation.truncate {G : Grammar} (t : Truncation G) {e : G.Ent}
    {l : Level (G.entry e)} (expr : Expr G e l) : t.eInt e :=
  Expr.truncate t expr

/-! ## `Lift`: placing a full expression into a tighter hole

The inverse direction (rebuilding an `Expr` from a semantic value) repeatedly
needs to take a full, loosest subexpression and drop it into a hole that demands
a *tighter* level — adding parentheses exactly when precedence forbids the direct
embedding. `Lift` is the data for that, kept **purely syntactic** (no `eInt`): it
is grammar-level and composes with any `Truncation`.

The precedence test `fits` is **user-supplied** so it can beat searching the
`tighter` graph (e.g. compare a precomputed numeric rank). It is not trusted: the
law `fits_iff` forces it to coincide with the real precedence relation
`Level.condition`, so a wrong `fits` is simply not a `Lift`. The `wrap`
(parenthesizer) is user data too, pinned to genuinely bracket its argument by
`wrap_flatten`.

**Single-level entries cost nothing.** When an entry has one inhabited level
(e.g. a variable sub-language, `Op = Empty`), `tighter`/`tighterEq` are
uninhabited, so `fits` is only ever asked at `.loosest` (vacuously / always
`true`) and `wrap` is never reached — supply `fits := fun _ _ => true`,
`wrap := fun _ x => x`, `bracket := ([], [])` and the laws hold trivially. -/
structure Lift (G : Grammar) where
  /-- A possibly-fast precedence test: does operator `o` sit at level `l`? -/
  fits : {e : G.Ent} → Level (G.entry e) → (G.entry e).Op → Bool
  /-- `fits` must agree with the real precedence relation — this is what forces a
  fast `fits` to be *correct*. -/
  fits_iff : ∀ {e : G.Ent} (l : Level (G.entry e)) (o : (G.entry e).Op),
    fits l o = true ↔ Level.condition l o
  /-- The bracket tokens an entry wraps with, e.g. `(["("], [")"])`. -/
  bracket : (e : G.Ent) → List Token × List Token
  /-- The parenthesizer: place a full expression at *any* level by bracketing. -/
  wrap : {e : G.Ent} → (l : Level (G.entry e)) → Expr G e .loosest → Expr G e l
  /-- `wrap` genuinely brackets: it flattens to `‹lb› ++ x ++ ‹rb›`. -/
  wrap_flatten : ∀ {e : G.Ent} (l : Level (G.entry e)) (x : Expr G e .loosest),
    (wrap l x).flatten = (bracket e).1 ++ x.flatten ++ (bracket e).2

/-- Coerce a full (loosest) expression into the level a hole demands: reindex it
if its top operator already `fits`, otherwise `wrap` it in brackets. Variables
fit every level, so they pass through untouched. -/
def Expr.lift {G : Grammar} (L : Lift G) {e : G.Ent} :
    (l : Level (G.entry e)) → Expr G e .loosest → Expr G e l
  | _, .var t h => .var t h
  | l, .op o hc parts =>
      if h : L.fits l o then .op o ((L.fits_iff l o).mp h) parts
      else L.wrap l (.op o hc parts)

/-- `lift` either leaves the flattening untouched (it fit, or it was a variable)
or surrounds it with the entry's brackets (it had to wrap). Either way no token is
lost or reordered — the only edit is a matched bracket pair. -/
theorem Expr.flatten_lift {G : Grammar} (L : Lift G) {e : G.Ent}
    (l : Level (G.entry e)) (x : Expr G e .loosest) :
    (Expr.lift L l x).flatten = x.flatten ∨
      (Expr.lift L l x).flatten = (L.bracket e).1 ++ x.flatten ++ (L.bracket e).2 := by
  cases x with
  | var t h => exact Or.inl rfl
  | op o hc parts =>
      simp only [Expr.lift]
      split
      · exact Or.inl rfl
      · exact Or.inr (L.wrap_flatten l (.op o hc parts))

end LambdaLab.Parser.Mixfix
