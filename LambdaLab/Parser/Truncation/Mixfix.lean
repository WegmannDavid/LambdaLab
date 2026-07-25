import LambdaLab.Parser.Truncation
import LambdaLab.Parser.IsoParser.Mixfix.Tree

/-!
# Mixfix truncation rules — instructions in, `LossyParser` out

`Parser/Truncation.lean` is fully general: any projection/injection pair with a section law. For
**mixfix trees** almost all of that pair is determined by the grammar; what a language actually
chooses is how each operator maps into its nicer target type. `Rules G C` bundles exactly those
choices, with laws calibrated to be *easily provable* for a concrete grammar:

* `var`/`op` — the **algebra**: what a variable leaf and each operator application mean in `C`.
  These clauses *are* the truncation instructions (`( e ) ↦ e`, `a + b ↦ add a b`, …).
* `dest` — the **coalgebra**: the canonical spelling of a target value (which operator, which
  operands). Vars and operators only — the paren operator never appears; parens are what
  truncation forgets.
* `parenOp`/`lp`/`rp`/`paren_eq` — the designated grouping operator (`paren_eq` is `rfl` for a
  concrete grammar).
* `holesOk`/`topOk` — grammar reachability conditions, `by decide` (via the fuel-based
  decidability of the precedence relations).
* `alg_dest` (destruct-then-rebuild is the identity — per-constructor `rfl`), `op_paren` (the
  paren clause projects — `rfl`), and `size`/`dest_size` (operands shrink — `simp`+`omega`).

From the bundle, *everything else is derived generically*: the fold `truncExpr` (the shallow
structural recursion — the deep dependent matching lives only in the user's `op`/`dest` clauses,
over their own finite types), the canonical injection `injC` (vars bare, compound operands
wrapped in `parenOp`), the section theorem `trunc_inj`, and `Rules.truncateParser`, which chains
any aligned echoing `IsoParser` producing these trees into the `LossyParser` with the fiber
annotation.

Instantiation checklist for a language: one `DecidableEq (E.Op)` projection instance (TC will not
unfold `myEntry.Op` to the underlying enum by itself), then the bundle — see `Arith.lean`.
-/

set_option linter.dupNamespace false

namespace LambdaLab.Parser.Truncation.Mixfix

open LambdaLab.Parser.IsoParser (IsoParser)
open LambdaLab.Parser.IsoParser.Mixfix
open LambdaLab.Parser.LossyParser (LossyParser)

variable {Tok : Type}

/-! ## Operand vectors -/

/-- The entries of a body shape's holes, in order. -/
def holeEnts {G : Grammar Tok} : List (Part G) → List G.Ent
  | [] => []
  | .namePart _ :: ps => holeEnts ps
  | .hole e _ :: ps => e :: holeEnts ps

/-- A heterogeneous operand vector: one `C e` per hole entry. -/
def CVec {G : Grammar Tok} (C : G.Ent → Type) : List G.Ent → Type
  | [] => PUnit
  | e :: es => C e × CVec C es

/-- Pointwise predicate over an operand vector. -/
def CVec.All {G : Grammar Tok} {C : G.Ent → Type} (P : ∀ {e : G.Ent}, C e → Prop) :
    ∀ {es : List G.Ent}, CVec C es → Prop
  | [], _ => True
  | _ :: _, vs => P vs.1 ∧ CVec.All P vs.2

/-- Every hole level of a shape admits the designated paren operator of its entry. -/
def HolesOk {G : Grammar Tok} (pOp : (e : G.Ent) → (G.entry e).Op) : List (Part G) → Prop
  | [] => True
  | .namePart _ :: ps => HolesOk pOp ps
  | .hole e l :: ps => l.condition (pOp e) ∧ HolesOk pOp ps

instance decHolesOk {G : Grammar Tok} (pOp : (e : G.Ent) → (G.entry e).Op)
    [∀ e : G.Ent, DecidableEq (G.entry e).Op] :
    ∀ ps : List (Part G), Decidable (HolesOk pOp ps)
  | [] => .isTrue trivial
  | .namePart _ :: ps => decHolesOk pOp ps
  | .hole e l :: ps =>
      haveI : Decidable (HolesOk pOp ps) := decHolesOk pOp ps
      haveI : Decidable (l.condition (pOp e)) := inferInstance
      instDecidableAnd

/-! ## The bundle -/

/-- The canonical head of a target value: a variable, or an operator with operand values. -/
inductive Head (G : Grammar Tok) (C : G.Ent → Type) (e : G.Ent) where
  | var  : (t : Tok) → (G.entry e).isVar t = true → Head G C e
  | node : (o : (G.entry e).Op) → CVec C (holeEnts (Operator.body e o)) → Head G C e

/-- The paren operator's body has exactly one hole, at its own entry's loosest level. -/
theorem body_paren_shape {G : Grammar Tok} {e : G.Ent} {o : (G.entry e).Op} {lp rp : Tok}
    (h : (G.entry e).operator o = .closed (.cons lp e (.last rp))) :
    Operator.body e o = [.namePart lp, .hole e .loosest, .namePart rp] := by
  unfold Operator.body
  rw [h]
  rfl

/-- Its hole entries: exactly `[e]`. -/
theorem holeEnts_paren {G : Grammar Tok} {e : G.Ent} {o : (G.entry e).Op} {lp rp : Tok}
    (h : (G.entry e).operator o = .closed (.cons lp e (.last rp))) :
    holeEnts (Operator.body e o) = [e] := by
  rw [body_paren_shape h]
  rfl

/-- The single-operand vector of the paren operator (a cast is inevitable over an abstract
grammar; for a concrete grammar `paren_eq` is `rfl`, both sides reduce, and proof irrelevance
makes this definitionally `(y, ())`). -/
def parenVec {G : Grammar Tok} {C : G.Ent → Type} {e : G.Ent} {o : (G.entry e).Op} {lp rp : Tok}
    (h : (G.entry e).operator o = .closed (.cons lp e (.last rp))) (y : C e) :
    CVec C (holeEnts (Operator.body e o)) :=
  (holeEnts_paren h).symm ▸ ((y, PUnit.unit) : CVec C [e])

/-- **The truncation instructions.** Everything a language chooses; every law is `rfl`-,
`decide`-, or `omega`-shaped for a concrete grammar. -/
structure Rules (G : Grammar Tok) (C : G.Ent → Type) where
  /-- A variable leaf, in the target. -/
  var : {e : G.Ent} → (t : Tok) → (G.entry e).isVar t = true → C e
  /-- An operator application, in the target — the truncation clauses. -/
  op : {e : G.Ent} → (o : (G.entry e).Op) → CVec C (holeEnts (Operator.body e o)) → C e
  /-- The canonical spelling of a target value. Never emits `parenOp`. -/
  dest : {e : G.Ent} → C e → Head G C e
  /-- The designated grouping operator of each entry… -/
  parenOp : (e : G.Ent) → (G.entry e).Op
  lp : G.Ent → Tok
  rp : G.Ent → Tok
  /-- …which is a closed `lp ‹e› rp` notation (`rfl` for a concrete grammar). -/
  paren_eq : ∀ e : G.Ent,
    (G.entry e).operator (parenOp e) = .closed (.cons (lp e) e (.last (rp e)))
  /-- Every hole level of every operator admits the paren operator (`by decide`). -/
  holesOk : ∀ (e : G.Ent) (o : (G.entry e).Op), HolesOk parenOp (Operator.body e o)
  /-- Every operator may appear at the loosest level (`by decide`). -/
  topOk : ∀ (e : G.Ent) (o : (G.entry e).Op), Level.condition (E := G.entry e) .loosest o
  /-- Destruct-then-rebuild is the identity (per-constructor `rfl`). -/
  alg_dest : ∀ {e : G.Ent} (x : C e),
    (match dest x with
      | .var t h => var t h
      | .node o vs => op o vs) = x
  /-- The paren clause projects its operand (`rfl`). -/
  op_paren : ∀ {e : G.Ent} (y : C e), op (parenOp e) (parenVec (paren_eq e) y) = y
  /-- A termination measure… -/
  size : {e : G.Ent} → C e → Nat
  /-- …under which canonical operands shrink (`simp` + `omega`). -/
  dest_size : ∀ {e : G.Ent} (x : C e),
    (match dest x with
      | .var _ _ => True
      | .node _ vs => CVec.All (fun y => size y < size x) vs)

variable {G : Grammar Tok} {C : G.Ent → Type}

/-! ## The derived fold (tree → target) -/

mutual
/-- Truncate a tree by the rules — the generic fold. -/
def truncExpr (R : Rules G C) : {e : G.Ent} → {l : Level (G.entry e)} → Expr G e l → C e
  | _, _, .var t h => R.var t h
  | _, _, .op o _ ps => R.op o (truncParts R ps)

def truncParts (R : Rules G C) : {shape : List (Part G)} → Parts G shape → CVec C (holeEnts shape)
  | _, .nil => PUnit.unit
  | _, @Parts.namePart _ _ s _ ps => truncParts R (shape := s) ps
  | _, @Parts.hole _ _ _ _ s ex ps => (truncExpr R ex, truncParts R (shape := s) ps)
end

/-! ## The derived injection (target → canonical tree) -/

/-- Wrap a loosest tree in the paren operator, placing it at any admissible level. -/
def wrapExpr {e : G.Ent} {o : (G.entry e).Op} {lp rp : Tok}
    (hsh : (G.entry e).operator o = .closed (.cons lp e (.last rp)))
    {l : Level (G.entry e)} (hp : l.condition o) (inner : Expr G e .loosest) : Expr G e l :=
  .op o hp ((body_paren_shape hsh).symm ▸
    (Parts.namePart lp (.hole inner (.namePart rp .nil)) :
      Parts G [.namePart lp, .hole e .loosest, .namePart rp]))

mutual
/-- The canonical tree of a target value: its `dest` spelling, operands via `operandExpr`. -/
def injC (R : Rules G C) {e : G.Ent} (x : C e) : Expr G e .loosest :=
  match hd : R.dest x with
  | .var t h => .var t h
  | .node o vs => .op o (R.topOk e o)
      (buildParts R (R.size x) (Operator.body e o) (R.holesOk e o) vs
        (by have h := R.dest_size x; rw [hd] at h; exact h))
termination_by (R.size x, 2, 0)

/-- Rebuild a body: name parts from the shape, operands from the vector. -/
def buildParts (R : Rules G C) (bound : Nat) :
    (shape : List (Part G)) → HolesOk R.parenOp shape →
    (vs : CVec C (holeEnts shape)) → CVec.All (fun y => R.size y < bound) vs → Parts G shape
  | [], _, _, _ => .nil
  | .namePart t :: ps, hok, vs, hsz => .namePart t (buildParts R bound ps hok vs hsz)
  | .hole _ l' :: ps, hok, vs, hsz =>
      .hole (operandExpr R bound l' hok.1 vs.1 hsz.1) (buildParts R bound ps hok.2 vs.2 hsz.2)
termination_by shape _ _ _ => (bound, 1, shape.length)

/-- An operand: bare if its head is a variable (vars inhabit every level), else its canonical
tree wrapped in the paren operator. -/
def operandExpr (R : Rules G C) (bound : Nat) {e' : G.Ent} (l' : Level (G.entry e'))
    (hp : l'.condition (R.parenOp e')) (y : C e') (_hy : R.size y < bound) : Expr G e' l' :=
  match R.dest y with
  | .var t h => .var t h
  | .node _ _ => wrapExpr (R.paren_eq e') hp (injC R y)
termination_by (bound, 0, 0)
end

/-! ## The section theorem, once and for all -/

/-- Truncating a cast is the cast of the truncation. -/
theorem truncParts_cast (R : Rules G C) {s1 s2 : List (Part G)} (h : s1 = s2) (ps : Parts G s1) :
    truncParts R (h ▸ ps) = (congrArg holeEnts h) ▸ truncParts R ps := by
  cases h; rfl

/-- Truncating a paren wrap: the paren clause applied to the inner truncation. -/
theorem truncExpr_wrap (R : Rules G C) {e : G.Ent} {o : (G.entry e).Op} {lp rp : Tok}
    (hsh : (G.entry e).operator o = .closed (.cons lp e (.last rp)))
    {l : Level (G.entry e)} (hp : l.condition o) (inner : Expr G e .loosest) :
    truncExpr R (wrapExpr hsh hp inner) = R.op o (parenVec hsh (truncExpr R inner)) := by
  rw [wrapExpr]
  simp only [truncExpr]
  rw [truncParts_cast]
  simp only [truncParts]
  rfl

mutual
/-- **The section law**: inject, truncate, recover — the witness `truncate` needs, derived from
the bundle's per-constructor laws. -/
theorem trunc_inj (R : Rules G C) : ∀ {e : G.Ent} (x : C e), truncExpr R (injC R x) = x
  | e, x => by
      simp only [injC]
      split
      · next t h hd =>
          simp only [truncExpr]
          have ha := R.alg_dest x
          rw [hd] at ha
          exact ha
      · next o vs hd =>
          simp only [truncExpr]
          rw [trunc_buildParts R (R.size x) (Operator.body e o)]
          have ha := R.alg_dest x
          rw [hd] at ha
          exact ha
termination_by _ x => (R.size x, 2, 0)

theorem trunc_buildParts (R : Rules G C) (bound : Nat) :
    ∀ (shape : List (Part G)) (hok : HolesOk R.parenOp shape)
      (vs : CVec C (holeEnts shape)) (hsz : CVec.All (fun y => R.size y < bound) vs),
      truncParts R (buildParts R bound shape hok vs hsz) = vs
  | [], _, _, _ => rfl
  | .namePart t :: ps, hok, vs, hsz => by
      simp only [buildParts, truncParts]
      exact trunc_buildParts R bound ps hok vs hsz
  | .hole _ l' :: ps, hok, vs, hsz => by
      simp only [buildParts, truncParts]
      rw [trunc_operand R bound l' hok.1 vs.1 hsz.1,
        trunc_buildParts R bound ps hok.2 vs.2 hsz.2]
      rfl
termination_by shape _ _ _ => (bound, 1, shape.length)

theorem trunc_operand (R : Rules G C) (bound : Nat) {e' : G.Ent} (l' : Level (G.entry e'))
    (hp : l'.condition (R.parenOp e')) (y : C e') (hy : R.size y < bound) :
    truncExpr R (operandExpr R bound l' hp y hy) = y := by
  simp only [operandExpr]
  split
  · next t h hd =>
      simp only [truncExpr]
      have ha := R.alg_dest y
      rw [hd] at ha
      exact ha
  · next hd =>
      rw [truncExpr_wrap, trunc_inj R y]
      exact R.op_paren y
termination_by (bound, 0, 0)
end

/-! ## The payoff -/

/-- **Instructions in, `LossyParser` out**: chain any aligned echoing `IsoParser` producing this
grammar's trees (e.g. `mixfix`) through the rules. The annotation is the fiber of the fold —
every tree spelling a target value; the canonical print is `injC`. -/
def Rules.truncateParser {α : Type} {fst fol : α → Prop} (R : Rules G C) {e : G.Ent}
    (p : IsoParser α fst fol (Expr G e .loosest) (Expr G e .loosest))
    (echo : ∀ a, (p.print a).1 = a) :
    LossyParser α fst fol (C e) (fun x => { t : Expr G e .loosest // truncExpr R t = x }) :=
  p.truncate echo (truncExpr R) (injC R) (fun x => trunc_inj R x)

end LambdaLab.Parser.Truncation.Mixfix
