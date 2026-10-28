import LambdaLab.Languages.CoC.Surface
import LambdaLab.Languages.CoC.DeBruijn.Check

/-!
# CoC — holes, and the solver that fills them

A definition may leave terms out: `_` is a term for the solver to find, `?A` one that every `?A`
of the definition shares. The solver fills them in; the checker then checks the filled definition
as if it had been written that way (`Pipeline.lean`'s `checkStep`).

## Holes are names

`_` and `?A` are word tokens, so the parser already reads them as names; nothing about the grammar
or the named calculus changes. A name is a hole where a term is expected (`isHoleName`); a binder
may carry one, and then binds nothing anyone can refer to. Translation into the core rejects holes
(`Pipeline.lean`'s `elabTm`), so a definition that translates has none left — which is all the
pipeline's laws need to know about them.

## The solver is not verified, and does not need to be

Whatever it returns is checked by the proved checker before it is accepted. A wrong or incomplete
solver therefore costs an error message, never an ill-typed definition: success is formalized,
failure is not — the same division as everywhere else in the pipeline.

What it does is the standard recipe:

* **elaboration, checking against what is expected** — a `λ` checked against a product takes its
  binder's type from it, so `λ x : _ . x` is solved by its context;
* **metavariables**: a `_` under binders `x₁ … xₖ` is a closed metavariable applied to them,
  `?m x₁ … xₖ`, so its solution may mention them. A `?A` is closed: it may not mention bound
  variables;
* **pattern unification**, up to β and to unfolding earlier definitions: `?m y₁ … yₙ ≡ t` with
  distinct bound variables `yᵢ` is solved by abstracting them out of `t`. Anything else is
  postponed and retried once more is known; what is still unsolved at the end is reported;
* **fuel**: terms may be ill-typed while holes are open, so nothing here is known to terminate —
  every recursion is bounded, and running out is an error.

The solutions are written back into the named source, so the filled definition reads as written:
earlier definitions by name, bound variables by their names, new binders named afresh.
-/

namespace LambdaLab.Languages.CoC

open LambdaLab.Parser.IsoParser
open LambdaLab.Pipeline (isFree)
open LambdaLab.Nominal (freshFor)
open LambdaLab.Languages.CoC.DeBruijn (Tm Srt)

/-! ## Holes, as names -/

/-- Is the name a hole: `_`, or `?` followed by more (`?A`, `?3`)? -/
def isHoleName (x : SName) : Bool :=
  match x.val.val.toList with
  | ['_'] => true
  | '?' :: _ :: _ => true
  | _ => false

/-- Does a hole occur where a term is expected? -/
def STm.hasHole : STm → Bool
  | .var x => isHoleName x
  | .sort _ => false
  | .pi _ A B => STm.hasHole A || STm.hasHole B
  | .lam _ A b => STm.hasHole A || STm.hasHole b
  | .app f a => STm.hasHole f || STm.hasHole a

/-- Does a hole occur in a definition? -/
def CDecl.hasHole (d : CDecl) : Bool := STm.hasHole d.ty || STm.hasHole d.tm

/-- An earlier definition, as checking keeps it: its name, its value translated (closed, the
definitions before it inlined), and its type as written. -/
structure Global where
  name : SName
  val : Tm
  ty : STm

namespace Holes

/-! ## What the solver reads and computes with -/

/-- A definition as the solver reads it: de Bruijn indices, earlier definitions by position, holes
marked. -/
inductive PTm where
  | var : Nat → PTm
  | sort : Srt → PTm
  | pi : String → PTm → PTm → PTm
  | lam : String → PTm → PTm → PTm
  | app : PTm → PTm → PTm
  | const : Nat → PTm
  /-- The `n`-th `_` of the definition. -/
  | hole : Nat → PTm
  /-- The `n`-th distinct `?name` of the definition. -/
  | named : Nat → PTm

/-- Terms with metavariables: the core's, earlier definitions by position, and closed
metavariables. -/
inductive MTm where
  | var : Nat → MTm
  | sort : Srt → MTm
  | pi : MTm → MTm → MTm
  | lam : MTm → MTm → MTm
  | app : MTm → MTm → MTm
  | const : Nat → MTm
  | mvar : Nat → MTm
  deriving BEq, Inhabited

namespace MTm

def ofTm : Tm → MTm
  | .var i => var i
  | .sort s => sort s
  | .pi A B => pi (ofTm A) (ofTm B)
  | .lam A b => lam (ofTm A) (ofTm b)
  | .app f a => app (ofTm f) (ofTm a)

def ren (ξ : Nat → Nat) : MTm → MTm
  | var i => var (ξ i)
  | pi A B => pi (A.ren ξ) (B.ren (DeBruijn.upRen ξ))
  | lam A b => lam (A.ren ξ) (b.ren (DeBruijn.upRen ξ))
  | app f a => app (f.ren ξ) (a.ren ξ)
  | t => t

def shift (t : MTm) : MTm := t.ren Nat.succ

def up (σ : Nat → MTm) : Nat → MTm
  | 0 => var 0
  | n + 1 => (σ n).shift

def subst (σ : Nat → MTm) : MTm → MTm
  | var i => σ i
  | pi A B => pi (A.subst σ) (B.subst (up σ))
  | lam A b => lam (A.subst σ) (b.subst (up σ))
  | app f a => app (f.subst σ) (a.subst σ)
  | t => t

/-- `b[0 := a]`. -/
def inst (b a : MTm) : MTm := b.subst (DeBruijn.scons a var)

def upRen? (ρ : Nat → Option Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => (ρ n).map (· + 1)

/-- Rename the free variables, failing on one the renaming does not cover. -/
def ren? (ρ : Nat → Option Nat) : MTm → Option MTm
  | var i => (ρ i).map var
  | pi A B => do pure (pi (← A.ren? ρ) (← B.ren? (upRen? ρ)))
  | lam A b => do pure (lam (← A.ren? ρ) (← b.ren? (upRen? ρ)))
  | app f a => do pure (app (← f.ren? ρ) (← a.ren? ρ))
  | t => some t

/-- Head and arguments. -/
def spine : MTm → MTm × List MTm
  | app f a => let p := f.spine; (p.1, p.2 ++ [a])
  | t => (t, [])

def apps (h : MTm) (as : List MTm) : MTm := as.foldl app h

def hasMeta (m : Nat) : MTm → Bool
  | mvar k => k == m
  | pi A B | lam A B | app A B => A.hasMeta m || B.hasMeta m
  | _ => false

/-- Does a variable bound outside the first `c` binders occur? -/
def hasFreeAbove (c : Nat) : MTm → Bool
  | var i => c ≤ i
  | pi A B | lam A B => A.hasFreeAbove c || B.hasFreeAbove (c + 1)
  | app f a => f.hasFreeAbove c || a.hasFreeAbove c
  | _ => false

def hasFree (n : Nat) : MTm → Bool
  | var i => i == n
  | pi A B | lam A B => A.hasFree n || B.hasFree (n + 1)
  | app f a => f.hasFree n || a.hasFree n
  | _ => false

/-- `?m` applied to the `k` variables in scope, outermost first. -/
def spineOf (m k : Nat) : MTm := (mvar m).apps ((List.range k).reverse.map var)

/-- `λⁿ. body` applied to `args`, at least `n` of them. -/
def instSol (n : Nat) (body : MTm) (args : List MTm) : MTm :=
  (body.subst (fun j => if j < n then args.getD (n - 1 - j) (var 0) else var (j - n))).apps
    (args.drop n)

/-! ### Printing, for messages -/

/-- `ns` names the variables in scope, innermost first, and `labels` the metavariables: `_` and
`?A` as written, `?` for the solver's own. Positions: `0` anywhere, `1` an arrow's operand, `2` a
function, `3` an argument. -/
def renderAt (gl : Array Global) (labels : Array String) : List String → Nat → MTm → String
  | ns, _, var i => ns.getD i s!"#{i}"
  | _, _, sort .star => "*"
  | _, _, sort .box => "□"
  | _, _, const g => (gl[g]?.map (fun e => e.name.val.val)).getD s!"#{g}"
  | _, _, mvar m => labels.getD m "?"
  | ns, p, pi A B =>
      let s :=
        if B.hasFree 0 then
          let x := s!"x{ns.length}"
          s!"Π {x} : {renderAt gl labels ns 0 A} . {renderAt gl labels (x :: ns) 0 B}"
        else s!"{renderAt gl labels ns 2 A} → {renderAt gl labels ("_" :: ns) 1 B}"
      if p > (if B.hasFree 0 then 0 else 1) then s!"({s})" else s
  | ns, p, lam A b =>
      let x := s!"x{ns.length}"
      let s := s!"λ {x} : {renderAt gl labels ns 0 A} . {renderAt gl labels (x :: ns) 0 b}"
      if p > 0 then s!"({s})" else s
  | ns, p, app f a =>
      let s := s!"{renderAt gl labels ns 2 f} {renderAt gl labels ns 3 a}"
      if p > 2 then s!"({s})" else s

end MTm

open MTm

/-! ## Translation into the solver's terms -/

/-- What translation keeps: how many `_` it has met, and the `?names` in order. -/
structure TSt where
  holes : Nat := 0
  named : List String := []

/-- The position of the most recent earlier definition called `x`, from `off` on. -/
def findGlobal (gl : Array Global) (off : Nat) (x : SName) : Option Nat :=
  ((gl.toList.drop off).findIdx? (·.name == x)).map (· + off)

/-- Translate: bound names to indices, earlier definitions (from position `off` on) to positions,
holes marked in order. -/
def toP (gl : Array Global) (off : Nat) : List SName → STm → StateT TSt (Except String) PTm
  | bs, .var x =>
      if isHoleName x then
        if x.val.val == "_" then
          modifyGet fun s => (.hole s.holes, { s with holes := s.holes + 1 })
        else
          modifyGet fun s => match s.named.idxOf? x.val.val with
            | some k => (.named k, s)
            | none => (.named s.named.length, { s with named := s.named ++ [x.val.val] })
      else
        match bs.idxOf? x with
        | some i => pure (.var i)
        | none =>
            match findGlobal gl off x with
            | some g => pure (.const g)
            | none => throw s!"`{x.val.val}` is neither bound nor an earlier definition"
  | _, .sort s => pure (.sort s)
  | bs, .pi x A B => do pure (.pi x.val.val (← toP gl off bs A) (← toP gl off (x :: bs) B))
  | bs, .lam x A b => do pure (.lam x.val.val (← toP gl off bs A) (← toP gl off (x :: bs) b))
  | bs, .app f a => do pure (.app (← toP gl off bs f) (← toP gl off bs a))

/-- A term read back as source, binders unnamed — so that `infer` can find its type. -/
def PTm.ofM? : MTm → Option PTm
  | .var i => some (.var i)
  | .sort s => some (.sort s)
  | .pi A B => do pure (.pi "x" (← PTm.ofM? A) (← PTm.ofM? B))
  | .lam A b => do pure (.lam "x" (← PTm.ofM? A) (← PTm.ofM? b))
  | .app f a => do pure (.app (← PTm.ofM? f) (← PTm.ofM? a))
  | .const g => some (.const g)
  | .mvar _ => none

/-- A hole-free translation, as a term. -/
def PTm.toM? : PTm → Option MTm
  | .var i => some (.var i)
  | .sort s => some (.sort s)
  | .pi _ A B => do pure (.pi (← A.toM?) (← B.toM?))
  | .lam _ A b => do pure (.lam (← A.toM?) (← b.toM?))
  | .app f a => do pure (.app (← f.toM?) (← a.toM?))
  | .const g => some (.const g)
  | .hole _ | .named _ => none

/-! ## The solver's state -/

structure Meta where
  arity : Nat
  sol : Option MTm := none

structure St where
  metas : Array Meta := #[]
  /-- Each `_`: its metavariable, and how many variables were in scope. -/
  holes : Array (Option (Nat × Nat)) := #[]
  /-- Each `?name`: its metavariable, and its type's. -/
  named : Array (Option (Nat × Nat)) := #[]
  /-- Equations put off until more is known, with the names in scope. -/
  postponed : List (List String × MTm × MTm) := []
  /-- The earlier definitions' types, once translated. -/
  types : Array (Option MTm) := #[]
  /-- Each `_`: the names and types in scope where it stands, and the type it must have. -/
  holeTypes : Array (Option (List String × List MTm × MTm)) := #[]
  /-- How each metavariable is shown: `_`, `?A`, or `?` for the solver's own. -/
  labels : Array String := #[]
  /-- The `?names`, in order. -/
  namedLabels : List String := []

abbrev M := StateT St (Except String)

def gaveUp : String := "gave up: solving the holes took too much computation"

/-- How far weak head normalization may go. -/
def whnfFuel : Nat := 5000

/-- How deep elaboration and unification may recurse. -/
def depthFuel : Nat := 2000

def newMeta (arity : Nat) (label : String := "?") : M Nat :=
  modifyGet fun s => (s.metas.size,
    { s with metas := s.metas.push { arity }, labels := s.labels.push label })

/-- Weak head normal form: β, solved metavariables at the head, and — with `δ` — earlier
definitions unfolded. -/
def whnf (st : St) (gl : Array Global) (δ : Bool) : Nat → MTm → MTm
  | 0, t => t
  | fuel + 1, t =>
      match t.spine with
      | (.lam _ b, a :: rest) => whnf st gl δ fuel ((b.inst a).apps rest)
      | (.mvar m, as) =>
          match st.metas[m]? with
          | some ⟨n, some body⟩ =>
              if n ≤ as.length then whnf st gl δ fuel (instSol n body as) else t
          | _ => t
      | (.const g, as) =>
          if δ then
            match gl[g]? with
            | some e => whnf st gl δ fuel ((MTm.ofTm e.val).apps as)
            | none => t
          else t
      | _ => t

/-- Instantiate every solved metavariable. -/
def zonk (st : St) : Nat → MTm → MTm
  | 0, t => t
  | fuel + 1, t =>
      match t.spine with
      | (.mvar m, as) =>
          match st.metas[m]? with
          | some ⟨n, some body⟩ =>
              if n ≤ as.length then zonk st fuel (instSol n body as)
              else (MTm.mvar m).apps (as.map (zonk st fuel))
          | _ => (MTm.mvar m).apps (as.map (zonk st fuel))
      | _ =>
          match t with
          | .pi A B => .pi (zonk st fuel A) (zonk st fuel B)
          | .lam A b => .lam (zonk st fuel A) (zonk st fuel b)
          | .app f a => .app (zonk st fuel f) (zonk st fuel a)
          | t => t

/-! ## Unification -/

def render (gl : Array Global) (ns : List String) (t : MTm) : M String := do
  let st ← get
  pure (renderAt gl st.labels ns 0 (zonk st depthFuel t))

/-- `?m y₁ … yₙ := rhs`, if that is a pattern: `n` is the arity and the `yᵢ` are distinct bound
variables. `false` when it is not one (yet). -/
def solvePattern (m : Nat) (args : List MTm) (rhs : MTm) : M Bool := do
  let st ← get
  let some ⟨n, none⟩ := st.metas[m]? | return false
  if args.length != n then return false
  let some vs := args.mapM (fun a => match a with | .var i => some i | _ => none) | return false
  if vs.eraseDups.length != vs.length then return false
  let rhs := zonk st depthFuel rhs
  if rhs.hasMeta m then return false
  match rhs.ren? (fun j => (vs.idxOf? j).map (n - 1 - ·)) with
  | some body =>
      set { st with metas := st.metas.set! m { arity := n, sol := some body } }
      return true
  | none => return false

def postpone (ns : List String) (a b : MTm) : M Unit :=
  modify fun s => { s with postponed := s.postponed ++ [(ns, a, b)] }

/-- An earlier definition unfolded at the head. -/
def unfoldHead (gl : Array Global) (t : MTm) : Option MTm :=
  match t.spine with
  | (.const g, as) => gl[g]?.map (fun e => (MTm.ofTm e.val).apps as)
  | _ => none

/-- **Make two terms equal**, up to β and unfolding, solving metavariables on the way. `ns` names
the variables in scope. -/
def unify (gl : Array Global) : List String → Nat → MTm → MTm → M Unit
  | _, 0, _, _ => throw gaveUp
  | ns, fuel + 1, a, b => do
      let st ← get
      let a := whnf st gl false whnfFuel a
      let b := whnf st gl false whnfFuel b
      if a == b then return
      let mismatch : M Unit := do
        throw s!"{← render gl ns a} and {← render gl ns b} do not match"
      let x := s!"x{ns.length}"
      match a.spine, b.spine with
      | (.mvar m, as), _ =>
          if ← solvePattern m as b then return
          match b.spine with
          | (.mvar m', bs) => if ← solvePattern m' bs a then return else postpone ns a b
          | _ => postpone ns a b
      | _, (.mvar m, bs) => if ← solvePattern m bs a then return else postpone ns a b
      | (.sort s, []), (.sort s', []) => if s == s' then return else mismatch
      | (.pi A B, []), (.pi A' B', []) => do
          unify gl ns fuel A A'
          unify gl (x :: ns) fuel B B'
      | (.lam A t, []), (.lam A' t', []) => do
          unify gl ns fuel A A'
          unify gl (x :: ns) fuel t t'
      | (.var i, as), (.var j, bs) =>
          if i == j && as.length == bs.length then
            for (u, v) in as.zip bs do unify gl ns fuel u v
          else mismatch
      | (.const g, as), (.const g', bs) =>
          let unfoldBoth : M Unit :=
            match unfoldHead gl a, unfoldHead gl b with
            | some a', some b' =>
                -- the more recent definition may be built from the other: unfold it first
                if g < g' then unify gl ns fuel a' b
                else if g' < g then unify gl ns fuel a b'
                else unify gl ns fuel a' b'
            | _, _ => mismatch
          if g == g' && as.length == bs.length then
            try
              for (u, v) in as.zip bs do unify gl ns fuel u v
            catch _ => unfoldBoth
          else unfoldBoth
      | (.const _, _), _ =>
          match unfoldHead gl a with
          | some a' => unify gl ns fuel a' b
          | none => mismatch
      | _, (.const _, _) =>
          match unfoldHead gl b with
          | some b' => unify gl ns fuel a b'
          | none => mismatch
      | _, _ => mismatch

/-- Retry the postponed equations while that solves something. -/
def retry (gl : Array Global) : Nat → M Unit
  | 0 => pure ()
  | n + 1 => do
      let st ← get
      if st.postponed.isEmpty then return
      let solved := (st.metas.toList.filter (·.sol.isSome)).length
      set { st with postponed := [] }
      for (ns, a, b) in st.postponed do unify gl ns depthFuel a b
      let st' ← get
      if (st'.metas.toList.filter (·.sol.isSome)).length == solved then return
      retry gl n

/-! ## Elaboration -/

/-- The type of an earlier definition, translated once. -/
def globalType (gl : Array Global) (g : Nat) : M MTm := do
  let st ← get
  if let some (some T) := st.types[g]? then return T
  let some e := gl[g]? | throw "internal: no such definition"
  let some T := (do
      let (P, _) ← ((toP gl (g + 1) [] e.ty).run {}).toOption
      P.toM?) | throw s!"internal: the type of `{e.name.val.val}` does not translate"
  let types := if st.types.size ≤ g then st.types ++ Array.replicate (g + 1 - st.types.size) none
    else st.types
  set { st with types := types.set! g (some T) }
  return T

/-- Is a term blocked on a metavariable? -/
def isFlex (t : MTm) : Bool :=
  match t.spine with
  | (.mvar _, _) => true
  | _ => false

/-- `s` is the type of `A`: it had better be a sort. -/
def ensureType (gl : Array Global) (ns : List String) (A s : MTm) : M Unit := do
  let s' := whnf (← get) gl true whnfFuel s
  match s' with
  | .sort _ => pure ()
  | _ => if isFlex s' then pure () else throw s!"{← render gl ns A} is not a type"

def recordHole (h m : Nat) (ns : List String) (Γ : List MTm) (T : MTm) : M Unit :=
  modify fun s => { s with
    holes := s.holes.set! h (some (m, Γ.length)),
    holeTypes := s.holeTypes.set! h (some (ns, Γ, T)) }

/-- The metavariable of a `?name`, and its type's: closed, one pair per name. -/
def namedMeta (n : Nat) : M (Nat × Nat) := do
  let st ← get
  if let some (some p) := st.named[n]? then return p
  let m ← newMeta 0 (st.namedLabels.getD n "?")
  let τ ← newMeta 0
  modify fun s => { s with named := s.named.set! n (some (m, τ)) }
  return (m, τ)

/-- `T'`, the type of `t`, must be `T`. A failure is reported here, with the types as they are
written, rather than wherever unfolding them led. -/
def expect (gl : Array Global) (ns : List String) (fuel : Nat) (t T' T : MTm) : M Unit := do
  try unify gl ns fuel T' T
  catch e =>
    if e == gaveUp then throw e
    throw s!"{← render gl ns t} has type {← render gl ns T'}, but {← render gl ns T} is expected"

/-- An unknown type `?m y₁ … yₙ` made a product within `?m`'s own scope, `?m := Π ?a . ?b`, so
that the domain and codomain may depend on no more than `?m` itself may. `false` if it is not a
pattern. -/
def makePi (m : Nat) (ys : List MTm) : M Bool := do
  let st ← get
  let some ⟨n, none⟩ := st.metas[m]? | return false
  let some vs := ys.mapM (fun y => match y with | .var i => some i | _ => none) | return false
  if vs.length != n || vs.eraseDups.length != n then return false
  let a ← newMeta n
  let b ← newMeta (n + 1)
  modify fun s => { s with
    metas := s.metas.set! m { arity := n, sol := some (.pi (spineOf a n) (spineOf b (n + 1))) } }
  return true

/-- A function's type, as a product — made one if it is still unknown. -/
def piOf (gl : Array Global) (Γ : List MTm) (ns : List String) (fuel : Nat) (f F : MTm) :
    M (MTm × MTm) := do
  let F' := whnf (← get) gl true whnfFuel F
  match F' with
  | .pi A B => pure (A, B)
  | _ =>
      if isFlex F' then
        if let (.mvar m, ys) := F'.spine then
          if ← makePi m ys then
            if let .pi A B := whnf (← get) gl true whnfFuel F' then return (A, B)
        let k := Γ.length
        let A := spineOf (← newMeta k) k
        let B := spineOf (← newMeta (k + 1)) (k + 1)
        unify gl ns fuel F' (.pi A B)
        pure (A, B)
      else throw s!"{← render gl ns f} is applied to an argument, but its type {← render gl ns F'} \
        is not a function type"

mutual

/-- **Infer**: the term, holes given metavariables, and its type. `Γ` holds the bound variables'
types, innermost first, each relative to the variables before it — as the core's contexts do. -/
def infer (gl : Array Global) (Γ : List MTm) (ns : List String) : Nat → PTm → M (MTm × MTm)
  | 0, _ => throw gaveUp
  | _ + 1, .var i =>
      match Γ[i]? with
      | some A => pure (.var i, A.ren (· + (i + 1)))
      | none => throw "internal: unbound variable"
  | _ + 1, .sort .star => pure (.sort .star, .sort .box)
  | _ + 1, .sort .box => throw "□ has no type, so it cannot stand where a term is expected"
  | _ + 1, .const g => do pure (.const g, ← globalType gl g)
  | fuel + 1, .pi x A B => do
      let (A', sA) ← infer gl Γ ns fuel A
      ensureType gl ns A' sA
      let (B', sB) ← infer gl (A' :: Γ) (x :: ns) fuel B
      match whnf (← get) gl true whnfFuel sB with
      | .sort s => pure (.pi A' B', .sort s)
      | _ => throw s!"{← render gl (x :: ns) B'} is not a type, or its sort cannot be inferred"
  | fuel + 1, .lam x A b => do
      let (A', sA) ← infer gl Γ ns fuel A
      ensureType gl ns A' sA
      let (b', B) ← infer gl (A' :: Γ) (x :: ns) fuel b
      pure (.lam A' b', .pi A' B)
  | fuel + 1, .app f a => do
      let (f', F) ← infer gl Γ ns fuel f
      let (A, B) ← piOf gl Γ ns fuel f' F
      let a' ← check gl Γ ns fuel a A
      pure (.app f' a', B.inst a')
  | _ + 1, .hole h => do
      let k := Γ.length
      let m ← newMeta k "_"
      let τ ← newMeta k
      recordHole h m ns Γ (spineOf τ k)
      pure (spineOf m k, spineOf τ k)
  | _ + 1, .named n => do
      let (m, τ) ← namedMeta n
      pure (.mvar m, .mvar τ)

/-- **Check** against an expected type: the term, holes given metavariables. -/
def check (gl : Array Global) (Γ : List MTm) (ns : List String) : Nat → PTm → MTm → M MTm
  | 0, _, _ => throw gaveUp
  | fuel + 1, .lam x A b, T => do
      match whnf (← get) gl true whnfFuel T with
      | .pi TA TB =>
          let (A', sA) ← infer gl Γ ns fuel A
          ensureType gl ns A' sA
          unify gl ns fuel A' TA
          let b' ← check gl (A' :: Γ) (x :: ns) fuel b TB
          pure (.lam A' b')
      | _ =>
          let (t', T') ← infer gl Γ ns fuel (.lam x A b)
          expect gl ns fuel t' T' T
          pure t'
  | _ + 1, .hole h, T => do
      let k := Γ.length
      let m ← newMeta k "_"
      recordHole h m ns Γ T
      pure (spineOf m k)
  | fuel + 1, t, T => do
      let (t', T') ← infer gl Γ ns fuel t
      expect gl ns fuel t' T' T
      pure t'

end

/-! ## Writing the solutions back -/

/-- A name from a string, if it is one. -/
def mkName? (s : String) : Option SName :=
  if h : isToken cocLex s = true then
    if h' : isFree cocReserved (⟨s, h⟩ : CTok) = true then some ⟨⟨s, h⟩, h'⟩ else none
  else none

/-- A name for a new binder: a conventional one if it is free — `A`, `B`, … over a sort, `x`, `y`,
… otherwise — else a fresh one. It avoids everything a readback beneath it could refer to. -/
def binderName (gl : Array Global) (bs : List SName) (overSort : Bool) : SName :=
  let avoid := bs ++ gl.toList.map (·.name)
  let cands := if overSort then ["A", "B", "C", "D", "E"] else ["x", "y", "z", "u", "v", "w"]
  match (cands.filterMap mkName?).find? (fun n => !avoid.contains n) with
  | some n => n
  | none => freshFor avoid

/-- Print a solved term in the named calculus, in a scope whose binders are `bs`. -/
def readback (gl : Array Global) (what : String) : List SName → Nat → MTm → Except String STm
  | _, 0, _ => throw gaveUp
  | bs, _ + 1, .var i =>
      match bs[i]? with
      | some x =>
          if isHoleName x then
            throw s!"{what} would refer to a variable whose binder is named `{x.val.val}`"
          else if (bs.take i).contains x then
            throw s!"{what} would refer to an outer `{x.val.val}`, which is shadowed there"
          else pure (.var x)
      | none => throw "internal: a solution is out of scope"
  | _, _ + 1, .sort s => pure (.sort s)
  | bs, fuel + 1, .const g =>
      match gl[g]? with
      | some e =>
          if !bs.contains e.name && findGlobal gl 0 e.name == some g then pure (.var e.name)
          else readback gl what bs fuel (MTm.ofTm e.val)
      | none => throw "internal: no such definition"
  | bs, fuel + 1, .pi A B => do
      let z := binderName gl bs (match A with | .sort _ => true | _ => false)
      let A' ← readback gl what bs fuel A
      let B' ← readback gl what (z :: bs) fuel B
      if B.hasFree 0 then pure (.pi z A' B') else pure (.pi (arrowName B') A' B')
  | bs, fuel + 1, .lam A b => do
      let z := binderName gl bs (match A with | .sort _ => true | _ => false)
      pure (.lam z (← readback gl what bs fuel A) (← readback gl what (z :: bs) fuel b))
  | bs, fuel + 1, .app f a => do
      pure (.app (← readback gl what bs fuel f) (← readback gl what bs fuel a))
  | _, _ + 1, .mvar _ => throw s!"{what} cannot be inferred: nothing here determines it"

/-- "1st", "2nd", … -/
def ordinal (n : Nat) : String :=
  let suffix :=
    if n % 100 ≥ 11 && n % 100 ≤ 13 then "th"
    else match n % 10 with | 1 => "st" | 2 => "nd" | 3 => "rd" | _ => "th"
  s!"{n}{suffix}"

/-- Replace the holes of the named source by their solutions, in translation order. -/
def fill (gl : Array Global) (st : St) (named : List String) :
    List SName → STm → StateT Nat (Except String) STm
  | bs, .var x =>
      if isHoleName x then
        if x.val.val == "_" then do
          let h ← modifyGet fun n => (n, n + 1)
          match st.holes[h]? with
          | some (some (m, k)) =>
              readback gl s!"the {ordinal (h + 1)} `_`" bs depthFuel
                (zonk st depthFuel (spineOf m k))
          | _ => throw "internal: a hole was never elaborated"
        else
          match st.named[named.idxOf x.val.val]? with
          | some (some (m, _)) =>
              readback gl s!"`{x.val.val}`" bs depthFuel (zonk st depthFuel (.mvar m))
          | _ => throw "internal: a named hole was never elaborated"
      else pure (.var x)
  | _, .sort s => pure (.sort s)
  | bs, .pi x A B => do pure (.pi x (← fill gl st named bs A) (← fill gl st named (x :: bs) B))
  | bs, .lam x A b => do pure (.lam x (← fill gl st named bs A) (← fill gl st named (x :: bs) b))
  | bs, .app f a => do pure (.app (← fill gl st named bs f) (← fill gl st named bs a))

/-- The message for equations left unsolved: most often a `?name`, which is closed, asked to be
something that mentions a bound variable. -/
def unsolvedMsg (gl : Array Global) (ns : List String) (a b : MTm) : M String := do
  let st ← get
  let closedNamed (t u : MTm) : Option String :=
    match zonk st depthFuel t with
    | .mvar m =>
        match st.metas[m]? with
        | some ⟨0, none⟩ =>
            let l := st.labels.getD m "?"
            if l.startsWith "?" && l.length > 1 && (zonk st depthFuel u).hasFreeAbove 0 then some l
            else none
        | _ => none
    | _ => none
  let hint := "a `?name` hole may not mention bound variables — write `_` instead"
  match closedNamed a b, closedNamed b a with
  | some l, _ => pure s!"`{l}` would have to be {← render gl ns b}, but {hint}"
  | _, some l => pure s!"`{l}` would have to be {← render gl ns a}, but {hint}"
  | none, none =>
      pure s!"cannot solve the holes: {← render gl ns a} and {← render gl ns b} must agree"

/-- **Each `_`'s solution has the type the `_` must have.** Unification alone does not see to
that, so it is checked once everything is solved, to say which hole is wrong before the checker
says only that the definition is. -/
def checkSolutions (gl : Array Global) : M Unit := do
  let st ← get
  for h in List.range st.holes.size do
    let some (some (m, k)) := st.holes[h]? | continue
    let some (some (ns, Γ, T)) := st.holeTypes[h]? | continue
    let sol := zonk (← get) depthFuel (spineOf m k)
    let some P := PTm.ofM? sol | continue
    let which := s!"the {ordinal (h + 1)} `_`"
    let T' ← try pure (← infer gl Γ ns depthFuel P).2
      catch _ => throw s!"{which} would be {← render gl ns sol}, which has no type"
    try unify gl ns depthFuel T' T
    catch _ => throw s!"{which} would be {← render gl ns sol}, of type {← render gl ns T'}, but it \
      must have type {← render gl ns T}"

end Holes

open Holes in
/-- **Fill the holes of a definition**, given the earlier ones, most recent first. Not verified:
what it returns is checked before it is accepted. -/
def fillHoles (s : List Global) (d : CDecl) : Except String CDecl := do
  let gl := s.toArray
  let ((tyP, tmP), ts) ← (do
      let tyP ← toP gl 0 [] d.ty
      let tmP ← toP gl 0 [] d.tm
      pure (tyP, tmP) : StateT TSt (Except String) (PTm × PTm)).run {}
  let st0 : St :=
    { holes := Array.replicate ts.holes none, named := Array.replicate ts.named.length none,
      holeTypes := Array.replicate ts.holes none, namedLabels := ts.named }
  let ((), st) ← (do
      let (ty', sTy) ← infer gl [] [] depthFuel tyP
      ensureType gl [] ty' sTy
      let _ ← check gl [] [] depthFuel tmP ty'
      retry gl 20
      if let some (ns, a, b) := (← get).postponed.head? then throw (← unsolvedMsg gl ns a b)
      checkSolutions gl
      : M Unit).run st0
  let (ty', n) ← (fill gl st ts.named [] d.ty).run 0
  let (tm', _) ← (fill gl st ts.named [] d.tm).run n
  pure { d with ty := ty', tm := tm' }

end LambdaLab.Languages.CoC
