import LambdaLab.Languages.CoIC.Surface
import LambdaLab.Languages.CoIC.DeBruijn.Check
import LambdaLab.Languages.CoIC.DeBruijn.Extend
import LambdaLab.Languages.CoIC.Named.Typing
import LambdaLab.Semantics.Walk

/-!
# CoIC — from what is written to what it means

The surface (`Surface.lean`) parses into `STm`; the checker and the evaluator run on the de Bruijn
core (`DeBruijn/`). This file connects them, and runs programs.

## The environment

An `inductive` declaration adds one entry to the **signature** (`DeBruijn.Sig`) and three kinds of
**global names**: the type (`Nat`), its constructors (`zero`, `succ`), and its recursor, named
after the type (`Nat_rec`). The signature only grows at the end, and stays valid
(`DeBruijn/Extend.lean`): every argument type is checked, over the signature before it, to be a
type naming only earlier inductives — or to be the new type itself, a recursive argument. The
names must be new, distinct, and not of the shape `x0, x1, …` that readback uses for binders
(`NamesFresh`); `TblOk` records what that buys, for every inductive at once.

Global names are constants: they resolve before bound names (`resolve`), so they cannot be
shadowed.

## Translation

`elabTm` translates a term, de Bruijn style: a bound name becomes its index, a global name its
meaning, and a defined name its value — definitions are transparent, and inlined; their values
are closed. Constructors and recursors are applied by name, `succ n`, `Nat_rec C z s n`, but the
core has them only **saturated**. So the translation tracks how many arguments a constant has
received (`Res`), and once it has all of them builds the saturated node (`Glob.sat`); a constant
used with fewer is its η-expansion (`Glob.fn`) applied to what it has. That is structural on the
term, and a term written with no globals translates exactly as the named calculus does
(`elab_eq_toDB`).

## Readback

`rb` prints a core term back: each binder named by its depth — `x0, x1, …` — except that a product
whose bound variable is unused gets the name `A → B` stands for, so it prints as an arrow; a
saturated constructor or recursor as its name applied to its arguments, an inductive as its name.
Reading the result back gives the term again (`elab_rb`), for every term that is consistent with
the signature (`Ok`; every well-typed term is, `HasType.ok`) and whose free variables are in
scope — closed ones in particular — which is what makes evaluation idempotent.

## Two walks

* **checking** (`checkWalk`): a definition is translated and its term checked against its declared
  type in the empty context; an inductive is checked and declared. It rewrites nothing. A
  definition is accepted exactly when its translation is well typed (`checkStep_iff`); with
  nothing declared before it, exactly when the *named* judgement holds of what was parsed
  (`checkStep_named`).
* **evaluation** (`evalWalk`), after checking: each definition's term, with the earlier
  definitions' values inlined, is normalized — total, by strong normalization — and written back.

Evaluation is idempotent a step at a time, and what it produces still checks (`evalRun_check`).
-/

namespace LambdaLab.Languages.CoIC

open LambdaLab.Pipeline
open LambdaLab.Parser.Numeral (isDigitChar natTok natOfTok isNatTok)
open LambdaLab.Semantics (Walk)
open LambdaLab.Nominal (freshFor freshFor_not_in)
open LambdaLab.Languages.CoIC.DeBruijn

/-! ## Name lookup -/

/-- The position of a name in a list, first occurrence. -/
def lookupIdx (n : SName) : List SName → Option Nat
  | [] => none
  | m :: ms => if m = n then some 0 else (lookupIdx n ms).map (· + 1)

theorem lookupIdx_eq_some {n : SName} : ∀ {l : List SName} {i : Nat},
    lookupIdx n l = some i → Named.lookupVar n l = i
  | [], _, h => by simp [lookupIdx] at h
  | m :: ms, i, h => by
      simp only [lookupIdx] at h
      by_cases hm : m = n
      · subst hm
        simp only [if_true, Option.some.injEq] at h
        subst h
        simp
      · rw [if_neg hm] at h
        cases hl : lookupIdx n ms with
        | none => simp [hl] at h
        | some j =>
            simp only [hl, Option.map_some, Option.some.injEq] at h
            subst h
            rw [Named.lookupVar_cons_ne _ (Ne.symm hm), lookupIdx_eq_some hl]

theorem lookupIdx_none {n : SName} : ∀ {l : List SName}, n ∉ l → lookupIdx n l = none
  | [], _ => rfl
  | m :: ms, h => by
      simp only [List.mem_cons, not_or] at h
      simp only [lookupIdx, if_neg (fun (e : m = n) => h.1 e.symm), lookupIdx_none h.2,
        Option.map_none]

theorem lookupIdx_getElem : ∀ {l : List SName}, l.Nodup → ∀ {k : Nat} (hk : k < l.length),
    lookupIdx l[k] l = some k
  | _ :: _, _, 0, _ => by simp [lookupIdx]
  | m :: ms, hnd, k + 1, hk => by
      have hnd' := List.nodup_cons.mp hnd
      have hk' : k < ms.length := by simp only [List.length_cons] at hk; omega
      have hne : m ≠ ms[k] := fun e => hnd'.1 (e ▸ List.getElem_mem hk')
      simp only [List.getElem_cons_succ, lookupIdx, if_neg hne, lookupIdx_getElem hnd'.2 hk',
        Option.map_some]

/-! ## Canonical names -/

theorem coic_digit_word : ∀ c, isDigitChar c = true → coicLex.word c = true :=
  LambdaLab.Parser.IsoParser.Lexicon.make_digit_word

/-- The name of the binder at depth `k`: `x0`, `x1`, … Never reserved, because no reserved token
has that shape. -/
def tmName (k : Nat) : SName :=
  ⟨natTok 'x' (by decide) coic_digit_word k, by
    show decide (natTok 'x' (by decide) coic_digit_word k ∉ coicReserved) = true
    rw [decide_eq_true_eq]
    intro hmem
    have h1 : ∀ r ∈ coicReserved, isNatTok 'x' r = false := by decide
    have h2 := h1 _ hmem
    rw [LambdaLab.Parser.Numeral.isNatTok_natTok] at h2
    cases h2⟩

theorem tmName_inj {j k : Nat} (h : tmName j = tmName k) : j = k := by
  have := congrArg (fun n : SName => natOfTok n.val) h
  simp only [tmName, LambdaLab.Parser.Numeral.natOfTok_natTok] at this
  exact this

/-- A name not of the shape `x<digits>` is no binder's. -/
theorem tmName_ne {x : SName} (hx : isNatTok 'x' x.val = false) (k : Nat) : tmName k ≠ x := by
  intro e
  subst e
  rw [show isNatTok 'x' (tmName k).val = true from
    LambdaLab.Parser.Numeral.isNatTok_natTok 'x' (by decide) coic_digit_word k] at hx
  cases hx

/-! ## Global names -/

/-- The names an inductive declaration introduces: the type's, the constructors', the
recursor's. -/
structure IndNames where
  ty : SName
  ctors : List SName
  elim : SName

/-- What a global name means. -/
inductive Glob
  | ind (i : Nat)
  | ctor (i k : Nat)
  | elim (i : Nat)
  deriving DecidableEq

/-- What `x` means among the names of the `i`-th inductive. -/
def IndNames.resolve (e : IndNames) (i : Nat) (x : SName) : Option Glob :=
  if e.ty = x then some (.ind i)
  else
    match lookupIdx x e.ctors with
    | some k => some (.ctor i k)
    | none => if e.elim = x then some (.elim i) else none

/-- What `x` means globally, the inductives numbered from `i`. -/
def resolve (x : SName) : List IndNames → Nat → Option Glob
  | [], _ => none
  | e :: es, i => (e.resolve i x).or (resolve x es (i + 1))

theorem resolve_append (x : SName) (e : IndNames) : ∀ (l : List IndNames) (j : Nat),
    resolve x (l ++ [e]) j = (resolve x l j).or (e.resolve (j + l.length) x)
  | [], j => by simp [resolve]
  | e' :: l, j => by
      simp only [List.cons_append, resolve, resolve_append x e l (j + 1), Option.or_assoc,
        List.length_cons]
      rw [show j + 1 + l.length = j + (l.length + 1) by omega]

/-- **The global names are in order**: each inductive's names resolve to it, and no binder name
resolves at all. -/
structure TblOk (sg : Sig) (tbl : List IndNames) : Prop where
  len : tbl.length = sg.length
  ctors : ∀ i (h : i < tbl.length), sg.numCtors i = some tbl[i].ctors.length
  ty : ∀ i (h : i < tbl.length), resolve tbl[i].ty tbl 0 = some (.ind i)
  ctor : ∀ i (h : i < tbl.length) k (hk : k < tbl[i].ctors.length),
    resolve tbl[i].ctors[k] tbl 0 = some (.ctor i k)
  elim : ∀ i (h : i < tbl.length), resolve tbl[i].elim tbl 0 = some (.elim i)
  bound : ∀ k, resolve (tmName k) tbl 0 = none

theorem TblOk.nil : TblOk [] [] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ => rfl⟩

/-- What a new inductive's names must be: unused, distinct, and not binder-shaped. -/
structure NamesFresh (tbl : List IndNames) (e : IndNames) : Prop where
  fresh : ∀ x ∈ e.ty :: e.elim :: e.ctors, resolve x tbl 0 = none
  nodup : (e.ty :: e.elim :: e.ctors).Nodup
  notTm : ∀ x ∈ e.ty :: e.elim :: e.ctors, isNatTok 'x' x.val = false

instance (tbl : List IndNames) (e : IndNames) : Decidable (NamesFresh tbl e) :=
  decidable_of_iff ((∀ x ∈ e.ty :: e.elim :: e.ctors, resolve x tbl 0 = none) ∧
      (e.ty :: e.elim :: e.ctors).Nodup ∧
      (∀ x ∈ e.ty :: e.elim :: e.ctors, isNatTok 'x' x.val = false))
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

theorem getElem_snoc_cases {α : Type} (l : List α) (e : α) {i : Nat}
    (hi : i < (l ++ [e]).length) :
    (∃ h : i < l.length, (l ++ [e])[i] = l[i]) ∨ (i = l.length ∧ (l ++ [e])[i] = e) := by
  by_cases h : i < l.length
  · exact .inl ⟨h, List.getElem_append_left h⟩
  · simp only [List.length_append, List.length_singleton] at hi
    have e' : i = l.length := by omega
    subst e'
    exact .inr ⟨rfl, by simp⟩

/-- **Declaring a checked inductive with fresh names keeps the global names in order.** -/
theorem TblOk.snoc {sg : Sig} {tbl : List IndNames} (h : TblOk sg tbl) {e : IndNames}
    (hf : NamesFresh tbl e) {cs : List CtorSpec} (hcs : ArgsOk sg cs)
    (hlen : e.ctors.length = cs.length) :
    TblOk (sg ++ [IndSpec.ofArgsOk cs hcs]) (tbl ++ [e]) := by
  have hnd := hf.nodup
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  obtain ⟨⟨hty_el, hty_cs⟩, hel_cs, hcsnd⟩ := hnd
  have old : ∀ x g, resolve x tbl 0 = some g → resolve x (tbl ++ [e]) 0 = some g := by
    intro x g hx
    rw [resolve_append, hx]
    rfl
  have new : ∀ x, x ∈ e.ty :: e.elim :: e.ctors →
      resolve x (tbl ++ [e]) 0 = e.resolve tbl.length x := by
    intro x hx
    rw [resolve_append, hf.fresh x hx, Nat.zero_add]
    rfl
  refine ⟨by simp [h.len], fun i hi => ?_, fun i hi => ?_, fun i hi k hk => ?_, fun i hi => ?_,
    fun k => ?_⟩
  · rcases getElem_snoc_cases tbl e hi with ⟨hi', he⟩ | ⟨rfl, he⟩
    · rw [he, Sig.numCtors_append _ (h.len ▸ hi')]
      exact h.ctors i hi'
    · rw [he, h.len, Sig.numCtors_snoc, hlen]
      rfl
  · rcases getElem_snoc_cases tbl e hi with ⟨hi', he⟩ | ⟨rfl, he⟩
    · rw [he]; exact old _ _ (h.ty i hi')
    · rw [he, new _ (by simp)]
      simp [IndNames.resolve]
  · rcases getElem_snoc_cases tbl e hi with ⟨hi', he⟩ | ⟨rfl, he⟩
    · have hk' : k < tbl[i].ctors.length := by simpa [he] using hk
      have : (tbl ++ [e])[i].ctors[k] = tbl[i].ctors[k] := by simp [he]
      rw [this]; exact old _ _ (h.ctor i hi' k hk')
    · have hk' : k < e.ctors.length := by simpa [he] using hk
      have : (tbl ++ [e])[tbl.length].ctors[k] = e.ctors[k] := by simp [he]
      rw [this, new _ (by simp [List.getElem_mem])]
      have hne : e.ty ≠ e.ctors[k] := fun eq => hty_cs (eq ▸ List.getElem_mem hk')
      simp only [IndNames.resolve, if_neg hne, lookupIdx_getElem hcsnd hk']
  · rcases getElem_snoc_cases tbl e hi with ⟨hi', he⟩ | ⟨rfl, he⟩
    · rw [he]; exact old _ _ (h.elim i hi')
    · rw [he, new _ (by simp)]
      simp only [IndNames.resolve, if_neg hty_el, lookupIdx_none hel_cs, if_true]
  · rw [resolve_append, h.bound k]
    show e.resolve (0 + tbl.length) (tmName k) = none
    have hty := tmName_ne (hf.notTm e.ty (by simp)) k
    have hrec := tmName_ne (hf.notTm e.elim (by simp)) k
    have hcs : tmName k ∉ e.ctors := fun hm =>
      tmName_ne (hf.notTm _ (by simp [hm])) k rfl
    simp only [IndNames.resolve, if_neg (Ne.symm hty), lookupIdx_none hcs, if_neg (Ne.symm hrec)]

/-- **What both walks carry about the inductives**: a valid signature, and its names in order. -/
structure Env where
  sg : Sig
  hsg : WfSig sg
  tbl : List IndNames
  htbl : TblOk sg tbl

/-- Nothing declared. -/
def Env.empty : Env :=
  ⟨[], fun _ _ _ h => by simp [Sig.ctorArgs] at h, [], TblOk.nil⟩

/-! ## The constants -/

/-- `λ A₁ … λ Aₙ . b`, the types as given. -/
def lams : List Tm → Tm → Tm
  | [], b => b
  | A :: As, b => .lam A (lams As b)

/-- `[var (n-1), …, var 0]`: the variables of `n` binders, outermost first. -/
def varsDown (n : Nat) : List Tm := (List.range n).reverse.map Tm.var

/-- How many arguments a constant takes before it is saturated. -/
def Glob.arity (sg : Sig) : Glob → Nat
  | .ind _ => 0
  | .ctor i k => ((sg.ctorArgs i k).map List.length).getD 0
  | .elim i => (sg.numCtors i).getD 0 + 2

/-- **The saturated node** of a constant and all its arguments. -/
def Glob.sat (sg : Sig) : Glob → List Tm → Tm
  | .ind i, _ => .ind i
  | .ctor i k, as => .ctor i k (((sg.ctorArgs i k).map CtorSpec.mask).getD []) (Tm.ofList as)
  | .elim i, C :: rest => .elim i C (Tm.ofList rest.dropLast) (rest.getLastD (.sort .star))
  | .elim _, [] => .sort .star

/-- **A constant on its own**: its η-expansion. A constructor abstracts its argument types; a
recursor its motive, a branch per constructor at its branch type, and the target. -/
def Glob.fn (sg : Sig) : Glob → Tm
  | .ind i => .ind i
  | .ctor i k =>
      match sg.ctorArgs i k with
      | some c => lams (c.map (argTy i)) (.ctor i k c.mask (Tm.ofList (varsDown c.length)))
      | none => .sort .star
  | .elim i =>
      match sg[i]? with
      | some I =>
          .lam (.sort .star)
            (lams (I.ctors.mapIdx fun k c => branchTy i c (.var k))
              (.lam (.ind i) (.elim i (.var (I.ctors.length + 1))
                (Tm.ofList (varsDown (I.ctors.length + 1)).dropLast) (.var 0))))
      | none => .sort .star

/-! ## Translation -/

/-- A translated term, or a constant still waiting for arguments. -/
inductive Res
  | tm (t : Tm)
  | part (g : Glob) (args : List Tm)

/-- What a result is as a term: a waiting constant is its η-expansion, applied. -/
def Res.toTm (sg : Sig) : Res → Tm
  | .tm t => t
  | .part g args => Tm.apps (g.fn sg) args

/-- A constant with these arguments: saturated once it has all of them. -/
def push (sg : Sig) (g : Glob) (args : List Tm) : Res :=
  if args.length = g.arity sg then .tm (g.sat sg args) else .part g args

/-- **Translate a term**: global names first, then bound names, then definitions. -/
def elabR (sg : Sig) (tbl : List IndNames) (bs : List SName) (gl : List (SName × Tm)) :
    STm → Option Res
  | .var x =>
      match resolve x tbl 0 with
      | some g => some (push sg g [])
      | none =>
          match lookupIdx x bs with
          | some i => some (.tm (.var i))
          | none => (gl.find? (fun p => p.1 = x)).map (fun p => .tm p.2)
  | .sort s => some (.tm (.sort s))
  | .pi x A B =>
      match elabR sg tbl bs gl A, elabR sg tbl (x :: bs) gl B with
      | some A', some B' => some (.tm (.pi (A'.toTm sg) (B'.toTm sg)))
      | _, _ => none
  | .lam x A b =>
      match elabR sg tbl bs gl A, elabR sg tbl (x :: bs) gl b with
      | some A', some b' => some (.tm (.lam (A'.toTm sg) (b'.toTm sg)))
      | _, _ => none
  | .app f a =>
      match elabR sg tbl bs gl f, elabR sg tbl bs gl a with
      | some (.part g args), some a' => some (push sg g (args ++ [a'.toTm sg]))
      | some (.tm f'), some a' => some (.tm (.app f' (a'.toTm sg)))
      | _, _ => none

/-- Translate a term. -/
def elabTm (sg : Sig) (tbl : List IndNames) (bs : List SName) (gl : List (SName × Tm))
    (t : STm) : Option Tm :=
  (elabR sg tbl bs gl t).map (Res.toTm sg)

/-- **With nothing declared, translation is the named calculus's**: a translation that succeeds is
`Named.Tm.toDB` of what was written. -/
theorem elabR_eq_toDB (sg : Sig) : ∀ (t : STm) (bs : List SName) (r : Res),
    elabR sg [] bs [] t = some r → r = .tm (t.toNamed.toDB bs)
  | .var x, bs, r, h => by
      simp only [elabR, resolve] at h
      split at h
      · rename_i i hi
        cases h
        simp only [STm.toNamed, Named.Tm.toDB, lookupIdx_eq_some hi]
      · simp at h
  | .sort _, _, _, h => by simp only [elabR, Option.some.injEq] at h; subst h; rfl
  | .pi x A B, bs, r, h => by
      simp only [elabR] at h
      split at h
      · rename_i A' B' hA hB
        cases h
        rw [elabR_eq_toDB sg A bs A' hA, elabR_eq_toDB sg B (x :: bs) B' hB]
        rfl
      · cases h
  | .lam x A b, bs, r, h => by
      simp only [elabR] at h
      split at h
      · rename_i A' b' hA hb
        cases h
        rw [elabR_eq_toDB sg A bs A' hA, elabR_eq_toDB sg b (x :: bs) b' hb]
        rfl
      · cases h
  | .app f a, bs, r, h => by
      simp only [elabR] at h
      split at h
      · rename_i g args a' hf _
        exact absurd (elabR_eq_toDB sg f bs _ hf) (by simp)
      · rename_i f' a' hf ha
        cases h
        cases elabR_eq_toDB sg f bs _ hf
        cases elabR_eq_toDB sg a bs _ ha
        rfl
      · cases h

theorem elab_eq_toDB (sg : Sig) (t : STm) (bs : List SName) (t' : Tm)
    (h : elabTm sg [] bs [] t = some t') : t' = t.toNamed.toDB bs := by
  simp only [elabTm, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  rw [elabR_eq_toDB sg t bs r hr]
  rfl

/-- **Applying a constant to its arguments one at a time** pushes them, in order. -/
theorem elabR_apps {sg : Sig} {tbl : List IndNames} {bs : List SName} {gl : List (SName × Tm)}
    (g : Glob) : ∀ (ps : List (STm × Tm)) (h : STm) (pre : List Tm),
      elabR sg tbl bs gl h = some (push sg g pre) → pre.length + ps.length ≤ g.arity sg →
      (∀ p ∈ ps, elabR sg tbl bs gl p.1 = some (.tm p.2)) →
      elabR sg tbl bs gl (STm.apps h (ps.map Prod.fst)) =
        some (push sg g (pre ++ ps.map Prod.snd))
  | [], h, pre, hh, _, _ => by simpa [STm.apps] using hh
  | p :: ps, h, pre, hh, hlen, hps => by
      have hlt : pre.length ≠ g.arity sg := by
        simp only [List.length_cons] at hlen; omega
      have hpart : push sg g pre = .part g pre := by simp [push, hlt]
      have happ : elabR sg tbl bs gl (.app h p.1) = some (push sg g (pre ++ [p.2])) := by
        simp only [elabR, hh, hpart, hps p (List.mem_cons_self ..), Res.toTm]
      have := elabR_apps g ps (.app h p.1) (pre ++ [p.2]) happ
        (by simp at hlen ⊢; omega)
        (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      simpa [STm.apps, List.append_assoc] using this

/-! ## Terms consistent with the signature -/

mutual
/-- **A term consistent with the signature**: inductives in range, constructors and recursors
with as many arguments as the signature says, and argument lists only where they belong. -/
def Ok (sg : Sig) : Tm → Prop
  | .var _ => True
  | .sort _ => True
  | .pi A B => Ok sg A ∧ Ok sg B
  | .lam A t => Ok sg A ∧ Ok sg t
  | .app t u => Ok sg t ∧ Ok sg u
  | .ind i => i < sg.length
  | .ctor i k m as =>
      (∃ c, sg.ctorArgs i k = some c ∧ m = c.mask ∧ as.toList.length = c.length) ∧ OkL sg as
  | .elim i C bs t =>
      (∃ n, sg.numCtors i = some n ∧ bs.toList.length = n) ∧ Ok sg C ∧ OkL sg bs ∧ Ok sg t
  | .tnil => False
  | .tcons _ _ => False

/-- An argument list of consistent terms. -/
def OkL (sg : Sig) : Tm → Prop
  | .tnil => True
  | .tcons a l => Ok sg a ∧ OkL sg l
  | _ => False
end

theorem OkL.isList {sg : Sig} : ∀ {l : Tm}, OkL sg l → l.isList = true
  | .tnil, _ => rfl
  | .tcons _ l, h => by
      simp only [OkL] at h
      exact OkL.isList (l := l) h.2
  | .var _, h => by simp [OkL] at h
  | .sort _, h => by simp [OkL] at h
  | .pi _ _, h => by simp [OkL] at h
  | .lam _ _, h => by simp [OkL] at h
  | .app _ _, h => by simp [OkL] at h
  | .ind _, h => by simp [OkL] at h
  | .ctor _ _ _ _, h => by simp [OkL] at h
  | .elim _ _ _ _, h => by simp [OkL] at h

theorem OkL.mem {sg : Sig} : ∀ {l a : Tm}, OkL sg l → a ∈ l.toList → Ok sg a
  | .tcons b l, a, h, hm => by
      simp only [OkL] at h
      simp only [Tm.toList, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact h.1
      · exact OkL.mem h.2 hm
  | .tnil, _, _, hm => by simp [Tm.toList] at hm
  | .var _, _, h, _ => by simp [OkL] at h
  | .sort _, _, h, _ => by simp [OkL] at h
  | .pi _ _, _, h, _ => by simp [OkL] at h
  | .lam _ _, _, h, _ => by simp [OkL] at h
  | .app _ _, _, h, _ => by simp [OkL] at h
  | .ind _, _, h, _ => by simp [OkL] at h
  | .ctor _ _ _ _, _, h, _ => by simp [OkL] at h
  | .elim _ _ _ _, _, h, _ => by simp [OkL] at h

theorem okL_of_nth {sg : Sig} : ∀ {l : Tm}, l.isList = true →
    (∀ j < l.toList.length, Ok sg (l.nth j)) → OkL sg l
  | .tnil, _, _ => by simp [OkL]
  | .tcons a l, hl, h => by
      simp only [OkL]
      refine ⟨h 0 (by simp [Tm.toList]), okL_of_nth (l := l) hl (fun j hj => ?_)⟩
      exact h (j + 1) (by simp [Tm.toList]; omega)
  | .var _, hl, _ => by simp [Tm.isList] at hl
  | .sort _, hl, _ => by simp [Tm.isList] at hl
  | .pi _ _, hl, _ => by simp [Tm.isList] at hl
  | .lam _ _, hl, _ => by simp [Tm.isList] at hl
  | .app _ _, hl, _ => by simp [Tm.isList] at hl
  | .ind _, hl, _ => by simp [Tm.isList] at hl
  | .ctor _ _ _ _, hl, _ => by simp [Tm.isList] at hl
  | .elim _ _ _ _, hl, _ => by simp [Tm.isList] at hl

/-- **Every well-typed term is consistent with its signature.** -/
theorem DeBruijn.HasType.ok {sg : Sig} {Γ : Ctx} {t T : Tm} (h : HasType sg Γ t T) : Ok sg t := by
  induction h with
  | sort => simp [Ok]
  | var => simp [Ok]
  | pi _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | lam _ _ _ ihA iht _ => exact ⟨ihA, iht⟩
  | app _ _ iht ihu => exact ⟨iht, ihu⟩
  | conv _ _ _ iht _ => exact iht
  | ind hi => exact hi
  | @ctor Γ i k mask as c hc hm hl hlen _ ih =>
      exact ⟨⟨c, hc, hm, hlen⟩, okL_of_nth hl (fun j hj => ih j (hlen ▸ hj))⟩
  | @elim Γ i m C bs t hm _ hl hlen _ _ _ ihC ihb _ iht =>
      refine ⟨⟨m, hm, hlen⟩, ihC, okL_of_nth hl (fun j hj => ?_), iht⟩
      obtain ⟨c, hc⟩ := Sig.ctorArgs_of_lt hm (hlen ▸ hj)
      exact ihb j c hc

theorem Tm.ofList_toList : ∀ {l : Tm}, l.isList = true → Tm.ofList l.toList = l
  | .tnil, _ => rfl
  | .tcons a l, hl => by
      simp only [Tm.toList, Tm.ofList, Tm.ofList_toList (l := l) hl]
  | .var _, hl => by simp [Tm.isList] at hl
  | .sort _, hl => by simp [Tm.isList] at hl
  | .pi _ _, hl => by simp [Tm.isList] at hl
  | .lam _ _, hl => by simp [Tm.isList] at hl
  | .app _ _, hl => by simp [Tm.isList] at hl
  | .ind _, hl => by simp [Tm.isList] at hl
  | .ctor _ _ _ _, hl => by simp [Tm.isList] at hl
  | .elim _ _ _ _, hl => by simp [Tm.isList] at hl

theorem Sig.ctorArgs_lt_numCtors {sg : Sig} {i k n : Nat} {c : CtorSpec}
    (hc : sg.ctorArgs i k = some c) (hn : sg.numCtors i = some n) : k < n := by
  simp only [Sig.ctorArgs, Option.bind_eq_some_iff] at hc
  simp only [Sig.numCtors, Option.map_eq_some_iff] at hn
  obtain ⟨I, hI, hk⟩ := hc
  obtain ⟨I', hI', rfl⟩ := hn
  rw [hI] at hI'
  cases hI'
  exact (List.getElem?_eq_some_iff.mp hk).1

/-! ## Readback -/

/-- Does the variable `n` occur free? -/
def DeBruijn.Tm.hasFree (n : Nat) : Tm → Bool
  | .var i => i == n
  | .sort _ => false
  | .pi A B => A.hasFree n || B.hasFree (n + 1)
  | .lam A t => A.hasFree n || t.hasFree (n + 1)
  | .app t u => t.hasFree n || u.hasFree n
  | .ind _ => false
  | .ctor _ _ _ as => as.hasFree n
  | .elim _ C bs t => C.hasFree n || bs.hasFree n || t.hasFree n
  | .tnil => false
  | .tcons a l => a.hasFree n || l.hasFree n

theorem Tm.hasFree_of_mem {n : Nat} : ∀ {l a : Tm}, a ∈ l.toList → a.hasFree n = true →
    l.hasFree n = true
  | .tcons b l, a, hm, ha => by
      simp only [Tm.toList, List.mem_cons] at hm
      simp only [Tm.hasFree, Bool.or_eq_true]
      rcases hm with rfl | hm
      · exact .inl ha
      · exact .inr (Tm.hasFree_of_mem hm ha)
  | .tnil, _, hm, _ => by simp [Tm.toList] at hm
  | .var _, _, hm, _ => by simp [Tm.toList] at hm
  | .sort _, _, hm, _ => by simp [Tm.toList] at hm
  | .pi _ _, _, hm, _ => by simp [Tm.toList] at hm
  | .lam _ _, _, hm, _ => by simp [Tm.toList] at hm
  | .app _ _, _, hm, _ => by simp [Tm.toList] at hm
  | .ind _, _, hm, _ => by simp [Tm.toList] at hm
  | .ctor _ _ _ _, _, hm, _ => by simp [Tm.toList] at hm
  | .elim _ _ _ _, _, hm, _ => by simp [Tm.toList] at hm

/-- The type's name. -/
def indName (tbl : List IndNames) (i : Nat) : SName := (tbl[i]?.map (·.ty)).getD (tmName 0)

/-- A constructor's name. -/
def ctorName (tbl : List IndNames) (i k : Nat) : SName :=
  (tbl[i]?.bind (·.ctors[k]?)).getD (tmName 0)

/-- The recursor's name. -/
def recName (tbl : List IndNames) (i : Nat) : SName := (tbl[i]?.map (·.elim)).getD (tmName 0)

mutual
/-- **Print a core term with names**: binders by depth, an unused product binder as an arrow's,
constructors and recursors applied by name. -/
def rb (tbl : List IndNames) (bs : List SName) : Tm → STm
  | .var i => .var (Named.nameAt bs i)
  | .sort s => .sort s
  | .pi A B =>
      if B.hasFree 0 then
        .pi (tmName bs.length) (rb tbl bs A) (rb tbl (tmName bs.length :: bs) B)
      else
        .pi (arrowName (rb tbl (tmName bs.length :: bs) B)) (rb tbl bs A)
          (rb tbl (tmName bs.length :: bs) B)
  | .lam A t => .lam (tmName bs.length) (rb tbl bs A) (rb tbl (tmName bs.length :: bs) t)
  | .app t u => .app (rb tbl bs t) (rb tbl bs u)
  | .ind i => .var (indName tbl i)
  | .ctor i k _ as => STm.apps (.var (ctorName tbl i k)) (rbL tbl bs as)
  | .elim i C bs' t =>
      STm.apps (.var (recName tbl i)) (rb tbl bs C :: (rbL tbl bs bs' ++ [rb tbl bs t]))
  | .tnil => .sort .star
  | .tcons _ _ => .sort .star

/-- Print an argument list. -/
def rbL (tbl : List IndNames) (bs : List SName) : Tm → List STm
  | .tcons a l => rb tbl bs a :: rbL tbl bs l
  | _ => []
end

theorem rbL_eq (tbl : List IndNames) (bs : List SName) :
    ∀ l : Tm, rbL tbl bs l = l.toList.map (rb tbl bs)
  | .tcons a l => by simp only [rbL, Tm.toList, List.map_cons, rbL_eq tbl bs l]
  | .tnil => by simp [rbL, Tm.toList]
  | .var _ => by simp [rbL, Tm.toList]
  | .sort _ => by simp [rbL, Tm.toList]
  | .pi _ _ => by simp [rbL, Tm.toList]
  | .lam _ _ => by simp [rbL, Tm.toList]
  | .app _ _ => by simp [rbL, Tm.toList]
  | .ind _ => by simp [rbL, Tm.toList]
  | .ctor _ _ _ _ => by simp [rbL, Tm.toList]
  | .elim _ _ _ _ => by simp [rbL, Tm.toList]

/-- The names of a term's free variables are where readback says: each free variable is named by
its depth, and nothing closer has that name. -/
def RbInv (bs : List SName) (t : Tm) : Prop :=
  ∀ i, t.hasFree i = true → i < bs.length ∧ Named.nameAt bs i = tmName (bs.length - 1 - i) ∧
    ∀ j < i, Named.nameAt bs j ≠ Named.nameAt bs i

theorem RbInv.sub {bs : List SName} {t s : Tm} (h : RbInv bs t)
    (hs : ∀ i, s.hasFree i = true → t.hasFree i = true) : RbInv bs s :=
  fun i hi => h i (hs i hi)

theorem lookupIdx_nameAt : ∀ {bs : List SName} {i : Nat}, i < bs.length →
    (∀ j < i, Named.nameAt bs j ≠ Named.nameAt bs i) → lookupIdx (Named.nameAt bs i) bs = some i
  | [], _, h, _ => by simp at h
  | b :: bs, 0, _, _ => by simp [Named.nameAt, lookupIdx]
  | b :: bs, i + 1, h, hne => by
      have hb : b ≠ Named.nameAt bs i := by
        have := hne 0 (by omega)
        simpa [Named.nameAt] using this
      simp only [Named.nameAt, lookupIdx, if_neg hb]
      rw [lookupIdx_nameAt (by simp only [List.length_cons] at h; omega) (fun j hj => by
        have := hne (j + 1) (by omega)
        simpa [Named.nameAt] using this)]
      rfl

/-- The invariant survives a binder named by depth. -/
theorem RbInv.cons_depth {bs : List SName} {t : Tm} (h : ∀ i, t.hasFree (i + 1) = true →
    i < bs.length ∧ Named.nameAt bs i = tmName (bs.length - 1 - i) ∧
      ∀ j < i, Named.nameAt bs j ≠ Named.nameAt bs i) :
    RbInv (tmName bs.length :: bs) t := by
  intro i hi
  cases i with
  | zero => exact ⟨by simp, by simp [Named.nameAt], fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i =>
      obtain ⟨hlt, hname, hne⟩ := h i hi
      refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
      · simp only [Named.nameAt, List.length_cons, hname]
        congr 1
        omega
      · intro j hj
        cases j with
        | zero =>
            simp only [Named.nameAt, hname]
            intro e
            have := tmName_inj e
            omega
        | succ j =>
            simp only [Named.nameAt]
            exact hne j (by omega)

/-- Readback depends only on the names of the free variables. -/
theorem rb_congr (tbl : List IndNames) : ∀ (t : Tm),
    (∀ (bs bs' : List SName), bs.length = bs'.length →
      (∀ i, t.hasFree i = true → Named.nameAt bs i = Named.nameAt bs' i) →
      rb tbl bs t = rb tbl bs' t) ∧
    (∀ (bs bs' : List SName), bs.length = bs'.length →
      (∀ i, t.hasFree i = true → Named.nameAt bs i = Named.nameAt bs' i) →
      rbL tbl bs t = rbL tbl bs' t) := by
  intro t
  induction t with
  | var i =>
      exact ⟨fun bs bs' _ h => by simp only [rb, h i (by simp [Tm.hasFree])],
        fun _ _ _ _ => by simp [rbL]⟩
  | sort => exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => by simp [rbL]⟩
  | pi A B ihA ihB =>
      refine ⟨fun bs bs' hl h => ?_, fun _ _ _ _ => by simp [rbL]⟩
      have hA := ihA.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))
      have hB := ihB.1 (tmName bs.length :: bs) (tmName bs.length :: bs') (by simp [hl])
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (by simp [Tm.hasFree, hi]))
      simp only [rb, hA, hB]
      rw [hl]
  | lam A t ihA iht =>
      refine ⟨fun bs bs' hl h => ?_, fun _ _ _ _ => by simp [rbL]⟩
      have hA := ihA.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))
      have ht := iht.1 (tmName bs.length :: bs) (tmName bs.length :: bs') (by simp [hl])
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (by simp [Tm.hasFree, hi]))
      simp only [rb, hA, ht]
      rw [hl]
  | app t u iht ihu =>
      refine ⟨fun bs bs' hl h => ?_, fun _ _ _ _ => by simp [rbL]⟩
      simp only [rb, iht.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi])),
        ihu.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))]
  | ind => exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => by simp [rbL]⟩
  | ctor i k m as ih =>
      refine ⟨fun bs bs' hl h => ?_, fun _ _ _ _ => by simp [rbL]⟩
      simp only [rb, ih.2 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))]
  | elim i C bs₀ t ihC ihbs iht =>
      refine ⟨fun bs bs' hl h => ?_, fun _ _ _ _ => by simp [rbL]⟩
      simp only [rb, ihC.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi])),
        ihbs.2 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi])),
        iht.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))]
  | tnil => exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => by simp [rbL]⟩
  | tcons a l iha ihl =>
      refine ⟨fun _ _ _ _ => rfl, fun bs bs' hl h => ?_⟩
      simp only [rbL, iha.1 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi])),
        ihl.2 bs bs' hl (fun i hi => h i (by simp [Tm.hasFree, hi]))]

theorem STm.mem_fv_apps {y : SName} : ∀ {h : STm} {xs : List STm},
    (y ∈ h.fv ∨ ∃ x ∈ xs, y ∈ x.fv) → y ∈ (STm.apps h xs).fv
  | _, [], hy => by
      rcases hy with hy | ⟨_, hx, _⟩
      · exact hy
      · simp at hx
  | h, a :: as, hy => by
      apply STm.mem_fv_apps (h := .app h a) (xs := as)
      rcases hy with hy | ⟨x, hx, hyx⟩
      · exact .inl (by simp [STm.fv, hy])
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl (by simp [STm.fv, hyx])
        · exact .inr ⟨x, hx, hyx⟩

/-- **A free variable's name is free in the readback.** -/
theorem rb_fv (sg : Sig) (tbl : List IndNames) : ∀ (t : Tm),
    (∀ bs, Ok sg t → RbInv bs t → ∀ i, t.hasFree i = true →
      Named.nameAt bs i ∈ (rb tbl bs t).fv) ∧
    (∀ bs, OkL sg t → RbInv bs t → ∀ i, t.hasFree i = true →
      ∃ x ∈ rbL tbl bs t, Named.nameAt bs i ∈ x.fv) := by
  intro t
  induction t with
  | var j =>
      refine ⟨fun bs _ _ i hi => ?_, fun _ h => by simp [OkL] at h⟩
      simp only [Tm.hasFree, beq_iff_eq] at hi
      subst hi
      simp [rb, STm.fv]
  | sort => exact ⟨fun _ _ _ _ hi => by simp [Tm.hasFree] at hi, fun _ h => by simp [OkL] at h⟩
  | pi A B ihA ihB =>
      refine ⟨fun bs hok hinv i hi => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hokA, hokB⟩ := hok
      have hB := RbInv.cons_depth (bs := bs) (t := B) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      have hne : Named.nameAt bs i ≠ tmName bs.length := by
        obtain ⟨hlt, hname, _⟩ := hinv i (by simp [Tm.hasFree, hi])
        rw [hname]
        intro e
        have := tmName_inj e
        omega
      unfold rb
      split
      · rcases hi with hi | hi
        · exact List.mem_append_left _ (ihA.1 bs hokA (hinv.sub (fun j hj => by
            simp [Tm.hasFree, hj])) i hi)
        · refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, by simpa using hne⟩)
          exact ihB.1 _ hokB hB (i + 1) hi
      · rcases hi with hi | hi
        · exact List.mem_append_left _ (ihA.1 bs hokA (hinv.sub (fun j hj => by
            simp [Tm.hasFree, hj])) i hi)
        · have hm := ihB.1 _ hokB hB (i + 1) hi
          refine List.mem_append_right _ (List.mem_filter.mpr ⟨hm, ?_⟩)
          simp only [decide_eq_true_eq]
          intro e
          exact freshFor_not_in _ (e ▸ hm)
  | lam A t ihA iht =>
      refine ⟨fun bs hok hinv i hi => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hokA, hokt⟩ := hok
      have ht := RbInv.cons_depth (bs := bs) (t := t) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      have hne : Named.nameAt bs i ≠ tmName bs.length := by
        obtain ⟨hlt, hname, _⟩ := hinv i (by simp [Tm.hasFree, hi])
        rw [hname]
        intro e
        have := tmName_inj e
        omega
      simp only [rb]
      rcases hi with hi | hi
      · exact List.mem_append_left _ (ihA.1 bs hokA (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) i hi)
      · refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, by simpa using hne⟩)
        exact iht.1 _ hokt ht (i + 1) hi
  | app t u iht ihu =>
      refine ⟨fun bs hok hinv i hi => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hokt, hoku⟩ := hok
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      simp only [rb, STm.fv]
      rcases hi with hi | hi
      · exact List.mem_append_left _ (iht.1 bs hokt (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) i hi)
      · exact List.mem_append_right _ (ihu.1 bs hoku (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) i hi)
  | ind => exact ⟨fun _ _ _ _ hi => by simp [Tm.hasFree] at hi, fun _ h => by simp [OkL] at h⟩
  | ctor i k m as ih =>
      refine ⟨fun bs hok hinv j hj => ?_, fun _ h => by simp [OkL] at h⟩
      simp only [Tm.hasFree] at hj
      simp only [rb]
      exact STm.mem_fv_apps (.inr (ih.2 bs hok.2 (hinv.sub (fun j hj => by
        simp [Tm.hasFree, hj])) j hj))
  | elim i C bs₀ t ihC ihbs iht =>
      refine ⟨fun bs hok hinv j hj => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨_, hokC, hokbs, hokt⟩ := hok
      simp only [Tm.hasFree, Bool.or_eq_true] at hj
      simp only [rb]
      refine STm.mem_fv_apps (.inr ?_)
      rcases hj with (hj | hj) | hj
      · exact ⟨_, List.mem_cons_self .., ihC.1 bs hokC (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) j hj⟩
      · obtain ⟨x, hx, hy⟩ := ihbs.2 bs hokbs (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) j hj
        exact ⟨x, List.mem_cons_of_mem _ (List.mem_append_left _ hx), hy⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)),
          iht.1 bs hokt (hinv.sub (fun j hj => by simp [Tm.hasFree, hj])) j hj⟩
  | tnil => exact ⟨fun _ h => by simp [Ok] at h, fun _ _ _ _ hi => by simp [Tm.hasFree] at hi⟩
  | tcons a l iha ihl =>
      refine ⟨fun _ h => by simp [Ok] at h, fun bs hok hinv j hj => ?_⟩
      simp only [OkL] at hok
      simp only [Tm.hasFree, Bool.or_eq_true] at hj
      simp only [rbL]
      rcases hj with hj | hj
      · exact ⟨_, List.mem_cons_self .., iha.1 bs hok.1 (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) j hj⟩
      · obtain ⟨x, hx, hy⟩ := ihl.2 bs hok.2 (hinv.sub (fun j hj => by
          simp [Tm.hasFree, hj])) j hj
        exact ⟨x, List.mem_cons_of_mem _ hx, hy⟩

theorem indName_eq {tbl : List IndNames} {i : Nat} (hi : i < tbl.length) :
    indName tbl i = tbl[i].ty := by
  simp [indName, List.getElem?_eq_getElem hi]

theorem ctorName_eq {tbl : List IndNames} {i k : Nat} (hi : i < tbl.length)
    (hk : k < tbl[i].ctors.length) : ctorName tbl i k = tbl[i].ctors[k] := by
  simp [ctorName, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hk]

theorem recName_eq {tbl : List IndNames} {i : Nat} (hi : i < tbl.length) :
    recName tbl i = tbl[i].elim := by
  simp [recName, List.getElem?_eq_getElem hi]

theorem map_pair_fst {α β : Type} (f : α → β) (l : List α) :
    (l.map (fun a => (f a, a))).map Prod.fst = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

theorem map_pair_snd {α β : Type} (f : α → β) (l : List α) :
    (l.map (fun a => (f a, a))).map Prod.snd = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

/-- **Reading a printed term back gives the term**, whatever definitions are in scope — none is
ever consulted, because every name is bound or global. -/
theorem elab_rb {sg : Sig} {tbl : List IndNames} (htbl : TblOk sg tbl) (gl : List (SName × Tm)) :
    ∀ (t : Tm),
      (∀ bs, Ok sg t → RbInv bs t → elabR sg tbl bs gl (rb tbl bs t) = some (.tm t)) ∧
      (∀ bs, OkL sg t → RbInv bs t → ∀ a ∈ t.toList,
        elabR sg tbl bs gl (rb tbl bs a) = some (.tm a)) := by
  intro t
  induction t with
  | var i =>
      refine ⟨fun bs _ hinv => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hlt, hname, hne⟩ := hinv i (by simp [Tm.hasFree])
      have hres : resolve (Named.nameAt bs i) tbl 0 = none := by rw [hname]; exact htbl.bound _
      simp only [rb, elabR, hres, lookupIdx_nameAt hlt hne]
  | sort => exact ⟨fun _ _ _ => rfl, fun _ h => by simp [OkL] at h⟩
  | pi A B ihA ihB =>
      refine ⟨fun bs hok hinv => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hokA, hokB⟩ := hok
      have hA := ihA.1 bs hokA (hinv.sub (fun j hj => by simp [Tm.hasFree, hj]))
      have hBinv := RbInv.cons_depth (bs := bs) (t := B) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      unfold rb
      split
      · simp only [elabR, hA, ihB.1 _ hokB hBinv, Res.toTm]
      · rename_i hB0
        -- the binder is unused, so the readback is the same under the arrow's name
        generalize hz : arrowName (rb tbl (tmName bs.length :: bs) B) = z
        have hzfresh : z ∉ (rb tbl (tmName bs.length :: bs) B).fv := hz ▸ freshFor_not_in _
        have hsame : rb tbl (tmName bs.length :: bs) B = rb tbl (z :: bs) B :=
          (rb_congr tbl B).1 _ _ (by simp) (fun i hi => by
            cases i with
            | zero => simp [hB0] at hi
            | succ i => rfl)
        have hzinv : RbInv (z :: bs) B := by
          intro i hi
          cases i with
          | zero => simp [hB0] at hi
          | succ i =>
              obtain ⟨hlt, hname, hne⟩ := hBinv (i + 1) hi
              refine ⟨hlt, by simpa [Named.nameAt] using hname, fun j hj => ?_⟩
              cases j with
              | zero =>
                  simp only [Named.nameAt]
                  intro e
                  have hm := (rb_fv sg tbl B).1 _ hokB hBinv (i + 1) hi
                  simp only [Named.nameAt] at hm
                  exact hzfresh (e ▸ hm)
              | succ j =>
                  have := hne (j + 1) hj
                  simpa [Named.nameAt] using this
        rw [hsame]
        simp only [elabR, hA, ihB.1 _ hokB hzinv, Res.toTm]
  | lam A t ihA iht =>
      refine ⟨fun bs hok hinv => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hokA, hokt⟩ := hok
      have hA := ihA.1 bs hokA (hinv.sub (fun j hj => by simp [Tm.hasFree, hj]))
      have htinv := RbInv.cons_depth (bs := bs) (t := t) (fun i hi => hinv i (by
        simp [Tm.hasFree, hi]))
      simp only [rb, elabR, hA, iht.1 _ hokt htinv, Res.toTm]
  | app t u iht ihu =>
      refine ⟨fun bs hok hinv => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨hokt, hoku⟩ := hok
      simp only [rb, elabR, iht.1 bs hokt (hinv.sub (fun j hj => by simp [Tm.hasFree, hj])),
        ihu.1 bs hoku (hinv.sub (fun j hj => by simp [Tm.hasFree, hj])), Res.toTm]
  | ind i =>
      refine ⟨fun bs hok _ => ?_, fun _ h => by simp [OkL] at h⟩
      have hi : i < tbl.length := htbl.len ▸ hok
      simp only [rb, elabR, indName_eq hi, htbl.ty i hi, push, Glob.arity, List.length_nil,
        if_true, Glob.sat]
  | ctor i k m as ih =>
      refine ⟨fun bs hok hinv => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨⟨c, hc, hm, hlen⟩, hokas⟩ := hok
      have hi : i < tbl.length := htbl.len ▸ Sig.ctorArgs_lt hc
      have hk : k < tbl[i].ctors.length := Sig.ctorArgs_lt_numCtors hc (htbl.ctors i hi)
      have harity : (Glob.ctor i k).arity sg = c.length := by simp [Glob.arity, hc]
      have hhead : elabR sg tbl bs gl (.var (ctorName tbl i k)) =
          some (push sg (.ctor i k) []) := by
        simp only [elabR, ctorName_eq hi hk, htbl.ctor i hi k hk]
      have hps : ∀ p ∈ as.toList.map (fun a => (rb tbl bs a, a)),
          elabR sg tbl bs gl p.1 = some (.tm p.2) := by
        intro p hp
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
        exact ih.2 bs hokas (hinv.sub (fun j hj => by simp [Tm.hasFree, hj])) a ha
      have := elabR_apps (.ctor i k) _ _ [] hhead (by simp [harity, hlen]) hps
      rw [map_pair_fst, map_pair_snd, List.nil_append] at this
      simp only [rb, rbL_eq]
      rw [this]
      simp only [push, harity, hlen, if_true, Glob.sat, hc, Option.map_some, Option.getD_some,
        ← hm, Tm.ofList_toList hokas.isList]
  | elim i C bs₀ t ihC ihbs iht =>
      refine ⟨fun bs hok hinv => ?_, fun _ h => by simp [OkL] at h⟩
      obtain ⟨⟨n, hn, hlen⟩, hokC, hokbs, hokt⟩ := hok
      have hi : i < tbl.length := htbl.len ▸ Sig.numCtors_lt hn
      have harity : (Glob.elim i).arity sg = n + 2 := by simp [Glob.arity, hn]
      have hhead : elabR sg tbl bs gl (.var (recName tbl i)) = some (push sg (.elim i) []) := by
        simp only [elabR, recName_eq hi, htbl.elim i hi]
      have hps : ∀ p ∈ (rb tbl bs C, C) :: (bs₀.toList.map (fun a => (rb tbl bs a, a)) ++
          [(rb tbl bs t, t)]), elabR sg tbl bs gl p.1 = some (.tm p.2) := by
        intro p hp
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | (⟨a, ha, rfl⟩ | rfl)
        · exact ihC.1 bs hokC (hinv.sub (fun j hj => by simp [Tm.hasFree, hj]))
        · exact ihbs.2 bs hokbs (hinv.sub (fun j hj => by simp [Tm.hasFree, hj])) a ha
        · exact iht.1 bs hokt (hinv.sub (fun j hj => by simp [Tm.hasFree, hj]))
      have := elabR_apps (.elim i) _ _ [] hhead (by simp [harity, hlen]) hps
      simp only [List.map_cons, List.map_append, map_pair_fst, map_pair_snd, List.map_nil,
        List.nil_append] at this
      simp only [rb, rbL_eq]
      rw [this]
      simp only [push, harity, List.length_cons, List.length_append,
        List.length_nil, hlen, if_true, Glob.sat, List.dropLast_concat, List.getLastD_concat,
        Tm.ofList_toList hokbs.isList]
  | tnil => exact ⟨fun _ h => by simp [Ok] at h, fun _ _ _ a ha => by simp [Tm.toList] at ha⟩
  | tcons a l iha ihl =>
      refine ⟨fun _ h => by simp [Ok] at h, fun bs hok hinv b hb => ?_⟩
      simp only [OkL] at hok
      simp only [Tm.toList, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact iha.1 bs hok.1 (hinv.sub (fun j hj => by simp [Tm.hasFree, hj]))
      · exact ihl.2 bs hok.2 (hinv.sub (fun j hj => by simp [Tm.hasFree, hj])) b hb

theorem DeBruijn.Tm.hasFree_lt : ∀ {t : Tm} {n i : Nat}, t.Scoped n → t.hasFree i = true → i < n
  | .var _, _, _, h, hi => by
      simp only [Tm.hasFree, beq_iff_eq] at hi
      subst hi
      exact h
  | .sort _, _, _, _, hi => by simp [Tm.hasFree] at hi
  | .pi _ _, _, i, ⟨hA, hB⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt hA hi
      · have := DeBruijn.Tm.hasFree_lt hB hi; omega
  | .lam _ _, _, i, ⟨hA, ht⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt hA hi
      · have := DeBruijn.Tm.hasFree_lt ht hi; omega
  | .app _ _, _, _, ⟨ht, hu⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt ht hi
      · exact DeBruijn.Tm.hasFree_lt hu hi
  | .ind _, _, _, _, hi => by simp [Tm.hasFree] at hi
  | .ctor _ _ _ as, _, _, h, hi => by
      simp only [Tm.hasFree] at hi
      exact DeBruijn.Tm.hasFree_lt (t := as) h hi
  | .elim _ _ _ _, _, _, ⟨hC, hbs, ht⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with (hi | hi) | hi
      · exact DeBruijn.Tm.hasFree_lt hC hi
      · exact DeBruijn.Tm.hasFree_lt hbs hi
      · exact DeBruijn.Tm.hasFree_lt ht hi
  | .tnil, _, _, _, hi => by simp [Tm.hasFree] at hi
  | .tcons _ _, _, _, ⟨ha, hl⟩, hi => by
      simp only [Tm.hasFree, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact DeBruijn.Tm.hasFree_lt ha hi
      · exact DeBruijn.Tm.hasFree_lt hl hi

/-- A closed, consistent term reads back and translates to itself. -/
theorem elab_rb_closed {sg : Sig} {tbl : List IndNames} (htbl : TblOk sg tbl) {t : Tm}
    (hok : Ok sg t) (h : t.Scoped 0) (gl : List (SName × Tm)) :
    elabTm sg tbl [] gl (rb tbl [] t) = some t := by
  simp only [elabTm, (elab_rb htbl gl t).1 [] hok
    (fun _ hi => absurd (DeBruijn.Tm.hasFree_lt h hi) (Nat.not_lt_zero _)), Option.map_some]
  rfl

/-! ## Declaring an inductive -/

/-- A term's application spine: its head and arguments. -/
def STm.spine : STm → STm × List STm
  | .app f a => (f.spine.1, f.spine.2 ++ [a])
  | t => (t, [])

/-- Is this the name `x`? -/
def STm.isName (x : SName) : STm → Bool
  | .var y => y == x
  | _ => false

/-- What an argument type may be: the new inductive itself, or a type over the earlier ones. -/
abbrev ArgOk (sg : Sig) (o : Option Tm) : Prop :=
  ∀ A, o = some A → HasType sg [] A (.sort .star) ∧ A.indsLt sg.length

/-- **Check one argument type**, the `k`-th of constructor `c`. -/
def checkArg (env : Env) (gl : List (SName × Tm)) (self c : SName) (k : Nat) (a : STm) :
    Except String {o : Option Tm // ArgOk env.sg o} :=
  if a.isName self then .ok ⟨none, fun _ h => by cases h⟩
  else
    match elabTm env.sg env.tbl [] gl a with
    | some A =>
        match decHasType env.hsg [] Wf.nil A (.sort .star), Tm.decIndsLt env.sg.length A with
        | isTrue h₁, isTrue h₂ => .ok ⟨some A, fun _ e => by cases e; exact ⟨h₁, h₂⟩⟩
        | isFalse _, _ => .error s!"argument {k + 1} of `{c.val.val}` is not a type in `*`"
        | _, isFalse _ =>
            .error s!"argument {k + 1} of `{c.val.val}` mentions an inductive type declared later"
    | none =>
        if self ∈ a.fv then
          .error s!"argument {k + 1} of `{c.val.val}` mentions `{self.val.val}` inside another \
            type: the type being declared may only be a whole argument"
        else .error s!"argument {k + 1} of `{c.val.val}` mentions a name that is not declared"

/-- Check a constructor's argument types, from the `k`-th on. -/
def checkArgs (env : Env) (gl : List (SName × Tm)) (self c : SName) :
    Nat → List STm → Except String {cs : CtorSpec // ∀ A, some A ∈ cs →
      HasType env.sg [] A (.sort .star) ∧ A.indsLt env.sg.length}
  | _, [] => .ok ⟨[], fun _ h => by simp at h⟩
  | k, a :: as =>
      match checkArg env gl self c k a with
      | .error m => .error m
      | .ok ⟨o, ho⟩ =>
          match checkArgs env gl self c (k + 1) as with
          | .error m => .error m
          | .ok ⟨cs, hc⟩ =>
              .ok ⟨o :: cs, fun A hA => by
                rcases List.mem_cons.mp hA with e | e
                · exact ho A e.symm
                · exact hc A e⟩

/-- Check the constructors, in order: each a name applied to its argument types. -/
def checkCtors (env : Env) (gl : List (SName × Tm)) (self : SName) :
    List STm → Except String {p : List SName × List CtorSpec //
      p.1.length = p.2.length ∧ ArgsOk env.sg p.2}
  | [] => .ok ⟨([], []), rfl, fun _ h => by simp at h⟩
  | t :: ts =>
      match t.spine with
      | (.var c, args) =>
          match checkArgs env gl self c 0 args with
          | .error m => .error m
          | .ok ⟨spec, hspec⟩ =>
              match checkCtors env gl self ts with
              | .error m => .error m
              | .ok ⟨(cs, specs), hlen, hok⟩ =>
                  .ok ⟨(c :: cs, spec :: specs), by simp [hlen], fun c' hc' => by
                    rcases List.mem_cons.mp hc' with rfl | hc'
                    · exact hspec
                    · exact hok c' hc'⟩
      | _ => .error "a constructor is written as its name applied to its argument types, like \
          `cons Nat List`"

/-- The recursor's name: the type's, with `_rec` after it. -/
def recNameOf (n : SName) : Option SName :=
  let s := n.val.val ++ "_rec"
  if h₁ : LambdaLab.Parser.IsoParser.isToken coicLex s = true then
    if h₂ : isCName ⟨s, h₁⟩ = true then some ⟨⟨s, h₁⟩, h₂⟩ else none
  else none

/-- Is a name unused by the definitions? -/
def notDefined (gl : List (SName × Tm)) (x : SName) : Bool := !(gl.any (fun p => p.1 == x))

/-- Why the names of an inductive declaration are not fresh. -/
def staleNameMsg (env : Env) (gl : List (SName × Tm)) (e : IndNames) : String :=
  let names := e.ty :: e.elim :: e.ctors
  match names.find? (fun x => isNatTok 'x' x.val) with
  | some x => s!"`{x.val.val}` has the shape of a name readback generates (`x0`, `x1`, …): \
      choose another"
  | none =>
      match names.find? (fun x => (resolve x env.tbl 0).isSome || !notDefined gl x) with
      | some x => s!"`{x.val.val}` is already declared"
      | none =>
          match names.find? (fun x => names.count x > 1) with
          | some x => s!"`{x.val.val}` is declared twice"
          | none => "the names of this declaration are not fresh"

/-- **Declare an inductive**: check its constructors over the current signature, name its
recursor, and add it — if its names are new. -/
def addInd (env : Env) (gl : List (SName × Tm)) (b : IndBody) : Except String Env :=
  match checkCtors env gl b.name b.ctors with
  | .error m => .error m
  | .ok p =>
      match recNameOf b.name with
      | none => .error s!"`{b.name.val.val}_rec`, the recursor's name, is not a valid name"
      | some r =>
          let e : IndNames := ⟨b.name, p.1.1, r⟩
          if hf : NamesFresh env.tbl e ∧ (e.ty :: e.elim :: e.ctors).all (notDefined gl) = true then
            .ok ⟨env.sg ++ [IndSpec.ofArgsOk p.1.2 p.2.2], env.hsg.snoc p.2.2, env.tbl ++ [e],
              env.htbl.snoc hf.1 p.2.2 p.2.1⟩
          else .error (staleNameMsg env gl e)

/-- Declaring only extends the signature. -/
theorem addInd_extends {env env' : Env} {gl : List (SName × Tm)} {b : IndBody}
    (h : addInd env gl b = .ok env') : ∃ sg', env'.sg = env.sg ++ sg' := by
  simp only [addInd] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h

/-! ## Checking -/

/-- Is a name free for a new definition? -/
def nameFree (env : Env) (gl : List (SName × Tm)) (x : SName) : Bool :=
  (resolve x env.tbl 0).isNone && notDefined gl x

/-- The diagnostic for a definition whose term does not have its type. -/
def illTypedMsg : String := "this definition does not have its declared type"

/-- The diagnostic for a definition that does not translate: its type, or else its term, names
something not declared before it. -/
def unknownNameMsg (inType : Bool) : String :=
  s!"{if inType then "the declared type" else "the term"} mentions a name that is not declared"

/-- **Check a definition**: its translated value, if it is well typed. -/
def checkDef (env : Env) (gl : List (SName × Tm)) (b : DefBody) : Except String Tm :=
  if nameFree env gl b.name then
    match elabTm env.sg env.tbl [] gl b.ty, elabTm env.sg env.tbl [] gl b.tm with
    | some T', some e' =>
        match decHasType env.hsg [] Wf.nil e' T' with
        | isTrue _ => .ok e'
        | isFalse _ => .error illTypedMsg
    | T', _ => .error (unknownNameMsg T'.isNone)
  else .error s!"`{b.name.val.val}` is already declared"

/-- What checking carries: the inductives, and each earlier definition's name and value. -/
abbrev CState := Env × List (SName × Tm)

/-- **Check one declaration.** It rewrites nothing. -/
def checkStep (s : CState) : CDecl → Except String (CDecl × CState)
  | .defn b => (checkDef s.1 s.2 b).map fun e' => (.defn b, (s.1, (b.name, e') :: s.2))
  | .ind b => (addInd s.1 s.2 b).map fun env => (.ind b, (env, s.2))

/-- **The checker**, as a walk. -/
def checkWalk : Walk CDecl where
  State := CState
  init := (Env.empty, [])
  step := checkStep

theorem checkStep_out {s : CState} {d d' : CDecl} {s' : CState}
    (h : checkStep s d = .ok (d', s')) : d' = d := by
  cases d with
  | defn b =>
      simp only [checkStep, Except.map_eq_ok_iff] at h
      obtain ⟨_, _, he⟩ := h
      cases he; rfl
  | ind b =>
      simp only [checkStep, Except.map_eq_ok_iff] at h
      obtain ⟨_, _, he⟩ := h
      cases he; rfl

theorem checkWalk_stepIdempotent : checkWalk.StepIdempotent := by
  intro s d d' s' h
  have h' : checkStep s d = .ok (d', s') := h
  have := checkStep_out h'
  subst this
  exact h

theorem checkWalk_idempotent : checkWalk.Idempotent :=
  checkWalk.idempotent_of_step checkWalk_stepIdempotent

/-- **A definition is accepted exactly when its name is free and its translation is well
typed.** -/
theorem checkDef_iff (env : Env) (gl : List (SName × Tm)) (b : DefBody) :
    (∃ v, checkDef env gl b = .ok v) ↔ nameFree env gl b.name = true ∧
      ∃ T' e', elabTm env.sg env.tbl [] gl b.ty = some T' ∧
        elabTm env.sg env.tbl [] gl b.tm = some e' ∧ HasType env.sg [] e' T' := by
  simp only [checkDef]
  constructor
  · rintro ⟨v, h⟩
    split at h
    · rename_i hfree
      refine ⟨hfree, ?_⟩
      split at h
      · rename_i T' e' hT he
        split at h
        · rename_i hty _
          exact ⟨T', e', hT, he, hty⟩
        · cases h
      · cases h
    · cases h
  · rintro ⟨hfree, T', e', hT, he, hty⟩
    simp only [hfree, if_true, hT, he]
    split
    · exact ⟨_, rfl⟩
    · rename_i hn _; exact absurd hty hn

/-- **With nothing declared before it, a definition the checker accepts is well typed in the named
calculus** — the parsed term at the parsed type, no translation in sight. -/
theorem checkDef_named {b : DefBody} (h : ∃ v, checkDef Env.empty [] b = .ok v) :
    Named.HasType [] [] b.tm.toNamed b.ty.toNamed := by
  obtain ⟨_, T', e', hT, he, hty⟩ := (checkDef_iff Env.empty [] b).mp h
  have e₁ := elab_eq_toDB [] b.ty [] T' hT
  have e₂ := elab_eq_toDB [] b.tm [] e' he
  subst e₁ e₂
  exact (Named.hasType_iff_toDB (Γ := []) trivial).mpr hty

/-! ## Evaluation -/

/-- An earlier definition, evaluated: its value, closed and normal. -/
structure EEntry where
  name : SName
  ty : Tm
  val : Tm
  normal : val.Normal

theorem EEntry.ext {a b : EEntry} (hn : a.name = b.name) (ht : a.ty = b.ty)
    (hv : a.val = b.val) : a = b := by
  cases a; cases b
  simp only at hn ht hv
  subst hn ht hv
  rfl

/-- What evaluation carries: the inductives, and the earlier definitions' values, typed over the
current signature. -/
structure EState where
  env : Env
  vals : List EEntry
  typed : ∀ e ∈ vals, HasType env.sg [] e.val e.ty

theorem EState.ext {a b : EState} (he : a.env = b.env) (hv : a.vals = b.vals) : a = b := by
  cases a; cases b
  simp only at he hv
  subst he hv
  rfl

/-- The values, as translation looks them up. -/
def EState.gl (s : EState) : List (SName × Tm) := s.vals.map (fun e => (e.name, e.val))

/-- **Evaluate a definition**: translate it with the earlier values inlined, check it, normalize
it — total, the closed term being well typed — and write it back with generated names. -/
def evalDef (s : EState) (b : DefBody) : Except String (CDecl × EState) :=
  if nameFree s.env s.gl b.name then
    match elabTm s.env.sg s.env.tbl [] s.gl b.ty, elabTm s.env.sg s.env.tbl [] s.gl b.tm with
    | some T', some e' =>
        match decHasType s.env.hsg [] Wf.nil e' T' with
        | isTrue h =>
            .ok (.defn ⟨b.name, b.ty, rb s.env.tbl [] (h.eval s.env.hsg Wf.nil)⟩,
              ⟨s.env, ⟨b.name, T', h.eval s.env.hsg Wf.nil,
                (Tm.eval_spec (h.sn s.env.hsg Wf.nil)).2⟩ :: s.vals, fun e he => by
                  rcases List.mem_cons.mp he with rfl | he
                  · exact h.eval_typed s.env.hsg Wf.nil
                  · exact s.typed e he⟩)
        | isFalse _ => .error illTypedMsg
    | T', _ => .error (unknownNameMsg T'.isNone)
  else .error s!"`{b.name.val.val}` is already declared"

/-- **Declare an inductive while evaluating**: as checking does; the values stay typed over the
longer signature. -/
def evalInd (s : EState) (b : IndBody) : Except String (CDecl × EState) :=
  match h : addInd s.env s.gl b with
  | .ok env' =>
      .ok (.ind b, ⟨env', s.vals, fun e he => by
        obtain ⟨sg', hsg'⟩ := addInd_extends h
        rw [hsg']
        exact (s.typed e he).extend sg'⟩)
  | .error m => .error m

/-- **Evaluate one declaration.** -/
def evalStep (s : EState) : CDecl → Except String (CDecl × EState)
  | .defn b => evalDef s b
  | .ind b => evalInd s b

/-- **The evaluator**, as a walk. -/
def evalWalk : Walk CDecl where
  State := EState
  init := ⟨Env.empty, [], fun _ h => by simp at h⟩
  step := evalStep

/-- What evaluating a definition does: it comes out as its value's readback, the value pushed. -/
theorem evalDef_sound {s : EState} {b : DefBody} {d' : CDecl} {s' : EState}
    (h : evalDef s b = .ok (d', s')) :
    ∃ e : EEntry, d' = .defn ⟨e.name, b.ty, rb s.env.tbl [] e.val⟩ ∧ e.name = b.name ∧
      nameFree s.env s.gl b.name = true ∧
      elabTm s.env.sg s.env.tbl [] s.gl b.ty = some e.ty ∧ s'.env = s.env ∧
      s'.vals = e :: s.vals := by
  simp only [evalDef] at h
  split at h
  · rename_i hfree
    split at h
    · rename_i T' e' hT he
      split at h
      · cases h
        exact ⟨_, rfl, rfl, hfree, hT, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

/-- **An evaluated definition evaluates to itself**: its readback reads back as its value, which
is closed, typed and normal. -/
theorem evalDef_reduced (s : EState) (T : STm) (e : EEntry)
    (hfree : nameFree s.env s.gl e.name = true)
    (hT : elabTm s.env.sg s.env.tbl [] s.gl T = some e.ty)
    (hty : HasType s.env.sg [] e.val e.ty) :
    ∃ s', evalDef s ⟨e.name, T, rb s.env.tbl [] e.val⟩ =
      .ok (.defn ⟨e.name, T, rb s.env.tbl [] e.val⟩, s') ∧ s'.env = s.env ∧
      s'.vals = e :: s.vals := by
  have hr : elabTm s.env.sg s.env.tbl [] s.gl (rb s.env.tbl [] e.val) = some e.val :=
    elab_rb_closed s.env.htbl hty.ok hty.scoped _
  refine ⟨⟨s.env, e :: s.vals, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hty
      · exact s.typed x hx⟩, ?_, rfl, rfl⟩
  simp only [evalDef, hfree, if_true, hT, hr]
  split
  · rename_i h _
    have hv : h.eval s.env.hsg Wf.nil = e.val := Tm.eval_of_normal _ e.normal
    refine congrArg Except.ok (Prod.ext ?_ (EState.ext rfl ?_))
    · dsimp only
      rw [hv]
    · exact congrArg (· :: s.vals) (EEntry.ext rfl rfl hv)
  · rename_i hn _
    exact absurd hty hn

/-- **Idempotence, a step at a time.** -/
theorem evalWalk_stepIdempotent : evalWalk.StepIdempotent := by
  intro s d d' s' h
  have h' : evalStep s d = .ok (d', s') := h
  show evalStep s d' = .ok (d', s')
  cases d with
  | ind b =>
      have : d' = .ind b := by
        simp only [evalStep, evalInd] at h'
        split at h'
        · cases h'; rfl
        · cases h'
      subst this
      exact h'
  | defn b =>
      obtain ⟨e, rfl, hn, hfree, hT, henv, hvals⟩ := evalDef_sound h'
      obtain ⟨s'', hs'', henv', hvals'⟩ := evalDef_reduced s b.ty e (hn ▸ hfree) hT
        (by have := s'.typed e (by rw [hvals]; exact List.mem_cons_self ..)
            rwa [henv] at this)
      have : s'' = s' := EState.ext (henv'.trans henv.symm) (hvals'.trans hvals.symm)
      subst this
      exact hs''

/-- What checking would carry, read off what evaluation carries. -/
def EState.proj (s : EState) : CState := (s.env, s.gl)

/-- **Evaluation's output checks**, a step at a time, in the corresponding state. -/
theorem evalStep_check {s : EState} {d d' : CDecl} {s' : EState}
    (h : evalStep s d = .ok (d', s')) : checkStep s.proj d' = .ok (d', s'.proj) := by
  cases d with
  | ind b =>
      simp only [evalStep, evalInd] at h
      split at h
      · rename_i env' hadd
        cases h
        simp only [checkStep, EState.proj, hadd, Except.map_ok_eq]
        rfl
      · cases h
  | defn b =>
      obtain ⟨e, rfl, hn, hfree, hT, henv, hvals⟩ := evalDef_sound h
      have hty : HasType s.env.sg [] e.val e.ty := by
        have := s'.typed e (by rw [hvals]; exact List.mem_cons_self ..)
        rwa [henv] at this
      have hr : elabTm s.env.sg s.env.tbl [] s.gl (rb s.env.tbl [] e.val) = some e.val :=
        elab_rb_closed s.env.htbl hty.ok hty.scoped _
      simp only [checkStep, checkDef, EState.proj]
      rw [hn]
      simp only [hfree, if_true, hT, hr]
      split
      · simp only [Except.map_ok_eq, Except.ok.injEq, Prod.mk.injEq, true_and]
        rw [henv]
        simp [EState.gl, hvals, hn]
      · rename_i hn' _
        exact absurd hty hn'

/-- **What evaluation produces still checks**: checking accepts evaluation's output a step at a
time (`evalStep_check`), so it accepts it whole (`Walk.runFrom_sim`). -/
theorem evalRun_check {p q : Program coicLanguage} (h : evalWalk.run p = .ok q) :
    checkWalk.run q = .ok q :=
  (Walk.run_eq_ok _).mpr (evalWalk.runFrom_sim checkWalk EState.proj
    (fun _ _ _ _ hs => evalStep_check hs) _ _ _ ((Walk.run_eq_ok _).mp h))

/-- **The law, as the stage after checking.** -/
theorem evalWalk_lawfulOn : evalWalk.LawfulOn (fun p => checkWalk.run p = .ok p) where
  preserve _ _ _ h := evalRun_check h
  idem p q _ h := evalWalk.idempotent_of_step evalWalk_stepIdempotent p q h

/-! ## The front end -/

/-- After evaluation: every definition's term in normal form. -/
abbrev evaluatedStage : LambdaLab.Abstraction.Stage :=
  coicLanguage.walkStageOn "evaluated program" evalWalk (fun p => checkWalk.run p = .ok p)

/-- **The whole front end, stage by stage**: source, tokens, program, checked program, evaluated
program. -/
def coicChain : LambdaLab.Abstraction.Chain sourceStage evaluatedStage :=
  (coicLanguage.walkChain checkWalk checkWalk_idempotent "checked program").cons
    (Z := evaluatedStage) (coicLanguage.walkCellOn evalWalk evalWalk_lawfulOn)

/-- **Characters to an evaluated program**, in `Abs`: one morphism, so one round-trip law. -/
def evalPipeline :=
  (coicLanguage.walkPipeline checkWalk checkWalk_idempotent).comp
    (evalWalk.stageOn evalWalk_lawfulOn)

/-- Read, check and evaluate a source file. -/
def evaluateFile (s : String) : Except Diag (evalWalk.FixedOn (fun p => checkWalk.run p = .ok p)) :=
  evalPipeline.abstract s.toList

/-- Render an evaluated program canonically. -/
def renderEvaluated (q : evalWalk.FixedOn (fun p => checkWalk.run p = .ok p)) : String :=
  String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))

/-- **The front end round-trips**: rendering an evaluated program and reading it back
re-tokenizes, re-parses, re-checks and re-evaluates to exactly what you started with. -/
theorem evaluateFile_renderEvaluated (q : evalWalk.FixedOn (fun p => checkWalk.run p = .ok p)) :
    evaluateFile (renderEvaluated q) = .ok q := by
  show evalPipeline.abstract
    (String.ofList (evalPipeline.realize (evalPipeline.default (a := q)))).toList = .ok q
  rw [String.toList_ofList]
  exact evalPipeline.abstract_realize q evalPipeline.default

end LambdaLab.Languages.CoIC
