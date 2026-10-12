import LambdaLab.Languages.CoIC.Named.Basic
import LambdaLab.Languages.CoIC.DeBruijn.Scope

/-!
# CoIC, named — the translation to de Bruijn, and back

`Tm.toDB ns` replaces each variable by its position in a list of binder names, innermost first
(`lookupVar`; a name absent from the list goes to the list's length). α-equivalent terms translate
to the same term, which is what lets every property proved of the de Bruijn core be read back here.

Two lemmas carry everything, each conditioned only on how the *free* variables are looked up:

* **renaming** (`Tm.toDB_ren`): translating against another binder list is renaming the
  translation. Taking `succ` gives that a binder the term does not mention is a shift
  (`Tm.toDB_insert`).
* **substitution** (`Tm.toDB_subst`): translating a named substitution is a de Bruijn substitution
  of the translation. Its binder cases are where capture-avoidance pays: a binder renamed away from
  what the substitution brings in is exactly what lets renaming shift those images under it.

β (`Tm.toDB_inst`) and renaming a bound name (`Tm.toDB_rename`) follow.

## Reading back

`fromDB ns t` gives a de Bruijn term names: the variables from `ns`, binders fresh. For a term
scoped in `ns` with `ns` free of repetitions, translating it back gives the term
(`Tm.toDB_fromDB`). The typing equivalence needs it: a de Bruijn derivation passes through types no
named term mentions, and they have to be given names.
-/

namespace LambdaLab.Languages.CoIC.Named

open LambdaLab.Nominal (Atom freshFor freshFor_not_in)
open LambdaLab.Languages.CoIC (DeBruijn.Tm)

variable {N : Type} [Atom N]

/-! ## Lookup -/

/-- The position of `x` among the binders `ns`, innermost first; `ns.length` if it is not
there. -/
def lookupVar (x : N) : List N → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else lookupVar x ys + 1

@[simp] theorem lookupVar_cons_self (x : N) (ns : List N) : lookupVar x (x :: ns) = 0 := by
  simp [lookupVar]

theorem lookupVar_cons_ne {x y : N} (ns : List N) (h : x ≠ y) :
    lookupVar x (y :: ns) = lookupVar x ns + 1 := by
  simp [lookupVar, Ne.symm h]

theorem lookupVar_lt_iff {x : N} : ∀ {ns : List N}, lookupVar x ns < ns.length ↔ x ∈ ns
  | [] => by simp [lookupVar]
  | y :: ys => by
      by_cases h : x = y
      · subst h; simp
      · rw [lookupVar_cons_ne _ h]
        simp only [List.length_cons, List.mem_cons, h, false_or]
        exact ⟨fun hl => lookupVar_lt_iff.mp (by omega), fun hm => by
          have := lookupVar_lt_iff.mpr hm; omega⟩

/-- The name at position `i`. -/
def nameAt : List N → Nat → N
  | [], _ => freshFor []
  | y :: _, 0 => y
  | _ :: ys, i + 1 => nameAt ys i

theorem nameAt_mem : ∀ {ns : List N} {i : Nat}, i < ns.length → nameAt ns i ∈ ns
  | [], _, h => by simp at h
  | _ :: _, 0, _ => by simp [nameAt]
  | _ :: ys, i + 1, h => by
      simp only [nameAt, List.mem_cons]
      exact .inr (nameAt_mem (by simp only [List.length_cons] at h; omega))

/-- In a list without repetitions, a name's position is where it is. -/
theorem lookupVar_nameAt : ∀ {ns : List N} {i : Nat}, ns.Nodup → i < ns.length →
    lookupVar (nameAt ns i) ns = i
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp [nameAt]
  | y :: ys, i + 1, hnd, h => by
      have hnd' := List.nodup_cons.mp hnd
      have hi : i < ys.length := by simp only [List.length_cons] at h; omega
      have hne : nameAt ys i ≠ y := fun e => hnd'.1 (e ▸ nameAt_mem hi)
      simp only [nameAt]
      rw [lookupVar_cons_ne _ hne, lookupVar_nameAt hnd'.2 hi]

/-! ## The translation -/

def Tm.toDB : List N → Tm N → DeBruijn.Tm
  | ns, .var x => .var (lookupVar x ns)
  | _, .sort s => .sort s
  | ns, .pi x A B => .pi (A.toDB ns) (B.toDB (x :: ns))
  | ns, .lam x A t => .lam (A.toDB ns) (t.toDB (x :: ns))
  | ns, .app t u => .app (t.toDB ns) (u.toDB ns)
  | _, .ind i => .ind i
  | ns, .ctor i k m as => .ctor i k m (as.toDB ns)
  | ns, .elim i C bs t => .elim i (C.toDB ns) (bs.toDB ns) (t.toDB ns)
  | _, .tnil => .tnil
  | ns, .tcons a l => .tcons (a.toDB ns) (l.toDB ns)

/-! ## Renaming -/

/-- **Renaming**: translating against other binders is renaming the translation, provided the free
variables are looked up consistently. -/
theorem Tm.toDB_ren : ∀ (t : Tm N) (ns ns' : List N) (ξ : Nat → Nat),
    (∀ x ∈ t.fv, lookupVar x ns' = ξ (lookupVar x ns)) → t.toDB ns' = (t.toDB ns).ren ξ
  | .var x, _, _, _, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren, h x (by simp [Tm.fv])]
  | .sort _, _, _, _, _ => rfl
  | .pi x A B, ns, ns', ξ, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren A ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_ren B (x :: ns) (x :: ns') (DeBruijn.upRen ξ) (fun y hy => by
          by_cases hyx : y = x
          · subst hyx; simp
          · rw [lookupVar_cons_ne _ hyx, lookupVar_cons_ne _ hyx,
              h y (by simp [Tm.fv, List.mem_filter, hy, hyx])]
            rfl)]
  | .lam x A t, ns, ns', ξ, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren A ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_ren t (x :: ns) (x :: ns') (DeBruijn.upRen ξ) (fun y hy => by
          by_cases hyx : y = x
          · subst hyx; simp
          · rw [lookupVar_cons_ne _ hyx, lookupVar_cons_ne _ hyx,
              h y (by simp [Tm.fv, List.mem_filter, hy, hyx])]
            rfl)]
  | .app t u, ns, ns', ξ, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren t ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_ren u ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy]))]
  | .ind _, _, _, _, _ => rfl
  | .ctor _ _ _ as, ns, ns', ξ, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren as ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy]))]
  | .elim _ C bs t, ns, ns', ξ, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren C ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_ren bs ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_ren t ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy]))]
  | .tnil, _, _, _, _ => rfl
  | .tcons a l, ns, ns', ξ, h => by
      simp only [Tm.toDB, DeBruijn.Tm.ren]
      rw [Tm.toDB_ren a ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_ren l ns ns' ξ (fun y hy => h y (by simp [Tm.fv, hy]))]

/-- A term does not notice a binder it does not mention. -/
theorem Tm.toDB_insert {t : Tm N} {z : N} (ns : List N) (h : z ∉ t.fv) :
    t.toDB (z :: ns) = (t.toDB ns).shift :=
  Tm.toDB_ren t ns (z :: ns) Nat.succ (fun _ hy => lookupVar_cons_ne _ (fun e => h (e ▸ hy)))

/-! ## Substitution -/

/-- **Substitution**: translating a named substitution is a de Bruijn substitution of the
translation, provided each free variable's image translates to what the de Bruijn substitution
puts at its position. -/
theorem Tm.toDB_subst : ∀ (t : Tm N) (ns ns' : List N) (τ : N → Tm N) (γ : Nat → DeBruijn.Tm),
    (∀ x ∈ t.fv, (τ x).toDB ns = γ (lookupVar x ns')) → (t.subst τ).toDB ns = (t.toDB ns').subst γ
  | .var x, _, _, _, _, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      exact h x (by simp [Tm.fv])
  | .sort _, _, _, _, _, _ => rfl
  | .pi x A B, ns, ns', τ, γ, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      generalize hz : pick x (avoidFor τ x B) = z
      have hfresh : z ∉ avoidFor τ x B := hz ▸ pick_not_mem _ _
      rw [Tm.toDB_subst A ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy]))]
      congr 1
      apply Tm.toDB_subst B (z :: ns) (x :: ns') (upd τ x (.var z)) (DeBruijn.Tm.up γ)
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp [Tm.toDB]
      · rw [upd_ne _ _ hyx, lookupVar_cons_ne _ hyx, DeBruijn.Tm.up_succ,
          Tm.toDB_insert ns (fun hw => hfresh (List.mem_flatMap.mpr
            ⟨y, by simp [List.mem_filter, hy, hyx], hw⟩)),
          h y (by simp [Tm.fv, List.mem_filter, hy, hyx])]
  | .lam x A t, ns, ns', τ, γ, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      generalize hz : pick x (avoidFor τ x t) = z
      have hfresh : z ∉ avoidFor τ x t := hz ▸ pick_not_mem _ _
      rw [Tm.toDB_subst A ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy]))]
      congr 1
      apply Tm.toDB_subst t (z :: ns) (x :: ns') (upd τ x (.var z)) (DeBruijn.Tm.up γ)
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp [Tm.toDB]
      · rw [upd_ne _ _ hyx, lookupVar_cons_ne _ hyx, DeBruijn.Tm.up_succ,
          Tm.toDB_insert ns (fun hw => hfresh (List.mem_flatMap.mpr
            ⟨y, by simp [List.mem_filter, hy, hyx], hw⟩)),
          h y (by simp [Tm.fv, List.mem_filter, hy, hyx])]
  | .app t u, ns, ns', τ, γ, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      rw [Tm.toDB_subst t ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_subst u ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy]))]
  | .ind _, _, _, _, _, _ => rfl
  | .ctor _ _ _ as, ns, ns', τ, γ, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      rw [Tm.toDB_subst as ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy]))]
  | .elim _ C bs t, ns, ns', τ, γ, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      rw [Tm.toDB_subst C ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_subst bs ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_subst t ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy]))]
  | .tnil, _, _, _, _, _ => rfl
  | .tcons a l, ns, ns', τ, γ, h => by
      simp only [Tm.subst, Tm.toDB, DeBruijn.Tm.subst]
      rw [Tm.toDB_subst a ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy])),
        Tm.toDB_subst l ns ns' τ γ (fun y hy => h y (by simp [Tm.fv, hy]))]

/-- **β commutes with the translation.** -/
theorem Tm.toDB_inst (b : Tm N) (x : N) (u : Tm N) (ns : List N) :
    (b.inst x u).toDB ns = (b.toDB (x :: ns)).inst (u.toDB ns) := by
  refine Tm.toDB_subst b ns (x :: ns) _ _ (fun y _ => ?_)
  by_cases h : y = x
  · subst h; simp
  · rw [upd_ne _ _ h, lookupVar_cons_ne _ h]
    rfl

/-- **Renaming a bound name** to one the body does not otherwise mention changes nothing the
translation sees. -/
theorem Tm.toDB_rename (b : Tm N) {x z : N} (ns : List N) (hz : z ∉ b.fv.filter (· ≠ x)) :
    (b.rename x z).toDB (z :: ns) = b.toDB (x :: ns) := by
  rw [Tm.rename, Tm.inst, Tm.toDB_subst b (z :: ns) (x :: ns) _ DeBruijn.Tm.var (fun y hy => by
      by_cases h : y = x
      · subst h; simp [Tm.toDB]
      · have hne : y ≠ z := fun e => hz (by subst e; simp [List.mem_filter, hy, h])
        rw [upd_ne _ _ h]
        simp only [Tm.toDB, lookupVar_cons_ne _ h, lookupVar_cons_ne _ hne]),
    DeBruijn.Tm.subst_var]

/-! ## Argument lists and the ι contractum -/

theorem Tm.toList_toDB : ∀ (l : Tm N) (ns : List N),
    (l.toDB ns).toList = l.toList.map (·.toDB ns)
  | .tcons a l, ns => by
      simp only [Tm.toDB, DeBruijn.Tm.toList, Tm.toList, Tm.toList_toDB l ns, List.map_cons]
  | .var _, _ => rfl
  | .sort _, _ => rfl
  | .pi _ _ _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .app _ _, _ => rfl
  | .ind _, _ => rfl
  | .ctor _ _ _ _, _ => rfl
  | .elim _ _ _ _, _ => rfl
  | .tnil, _ => rfl

theorem Tm.isList_toDB : ∀ (l : Tm N) (ns : List N), (l.toDB ns).isList = l.isList
  | .tcons _ l, ns => Tm.isList_toDB l ns
  | .var _, _ => rfl
  | .sort _, _ => rfl
  | .pi _ _ _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .app _ _, _ => rfl
  | .ind _, _ => rfl
  | .ctor _ _ _ _, _ => rfl
  | .elim _ _ _ _, _ => rfl
  | .tnil, _ => rfl

theorem Tm.nth_toDB (l : Tm N) (ns : List N) (k : Nat) :
    (l.toDB ns).nth k = (l.nth k).toDB ns := by
  simp only [DeBruijn.Tm.nth, Tm.nth, Tm.toList_toDB]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l.toList[k]? <;> rfl

theorem Tm.apps_toDB : ∀ (h : Tm N) (as : List (Tm N)) (ns : List N),
    (Tm.apps h as).toDB ns = DeBruijn.Tm.apps (h.toDB ns) (as.map (·.toDB ns))
  | _, [], _ => rfl
  | h, a :: as, ns => by
      simp only [Tm.apps, Tm.apps_toDB (.app h a) as ns, Tm.toDB, List.map_cons,
        DeBruijn.Tm.apps]

theorem Tm.recCalls_toDB (i : Nat) (C bs : Tm N) (ns : List N) :
    ∀ (as : List (Tm N)) (mask : List Bool),
      (Tm.recCalls i C bs as mask).map (·.toDB ns) =
        DeBruijn.Tm.recCalls i (C.toDB ns) (bs.toDB ns) (as.map (·.toDB ns)) mask
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, r :: mask => by
      have ih := Tm.recCalls_toDB i C bs ns as mask
      simp only [Tm.recCalls, DeBruijn.Tm.recCalls, List.zip_cons_cons, List.filterMap_cons]
        at ih ⊢
      cases r <;> simp [ih, Tm.toDB]

theorem Tm.iotaRhs_toDB (i : Nat) (C bs : Tm N) (k : Nat) (mask : List Bool) (as : Tm N)
    (ns : List N) :
    (Tm.iotaRhs i C bs k mask as).toDB ns =
      DeBruijn.Tm.iotaRhs i (C.toDB ns) (bs.toDB ns) k mask (as.toDB ns) := by
  simp only [Tm.iotaRhs, DeBruijn.Tm.iotaRhs, Tm.apps_toDB, Tm.nth_toDB, List.map_append,
    Tm.toList_toDB, Tm.recCalls_toDB]

/-! ## Scoping -/

/-- A term whose translation is scoped mentions only the names it was translated against. -/
theorem Tm.fv_of_scoped : ∀ (t : Tm N) (ns : List N), (t.toDB ns).Scoped ns.length →
    ∀ y ∈ t.fv, y ∈ ns
  | .var x, ns, h, y, hy => by
      simp only [Tm.fv, List.mem_singleton] at hy
      subst hy
      exact lookupVar_lt_iff.mp h
  | .sort _, _, _, _, hy => by simp [Tm.fv] at hy
  | .pi x A B, ns, ⟨hA, hB⟩, y, hy => by
      simp only [Tm.fv, List.mem_append, List.mem_filter, decide_eq_true_eq] at hy
      rcases hy with hy | ⟨hy, hne⟩
      · exact Tm.fv_of_scoped A ns hA y hy
      · have := Tm.fv_of_scoped B (x :: ns) hB y hy
        simpa [hne] using this
  | .lam x A t, ns, ⟨hA, ht⟩, y, hy => by
      simp only [Tm.fv, List.mem_append, List.mem_filter, decide_eq_true_eq] at hy
      rcases hy with hy | ⟨hy, hne⟩
      · exact Tm.fv_of_scoped A ns hA y hy
      · have := Tm.fv_of_scoped t (x :: ns) ht y hy
        simpa [hne] using this
  | .app t u, ns, ⟨ht, hu⟩, y, hy => by
      simp only [Tm.fv, List.mem_append] at hy
      rcases hy with hy | hy
      · exact Tm.fv_of_scoped t ns ht y hy
      · exact Tm.fv_of_scoped u ns hu y hy
  | .ind _, _, _, _, hy => by simp [Tm.fv] at hy
  | .ctor _ _ _ as, ns, h, y, hy => by
      simp only [Tm.fv] at hy
      exact Tm.fv_of_scoped as ns h y hy
  | .elim _ C bs t, ns, ⟨hC, hbs, ht⟩, y, hy => by
      simp only [Tm.fv, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · exact Tm.fv_of_scoped C ns hC y hy
      · exact Tm.fv_of_scoped bs ns hbs y hy
      · exact Tm.fv_of_scoped t ns ht y hy
  | .tnil, _, _, _, hy => by simp [Tm.fv] at hy
  | .tcons a l, ns, ⟨ha, hl⟩, y, hy => by
      simp only [Tm.fv, List.mem_append] at hy
      rcases hy with hy | hy
      · exact Tm.fv_of_scoped a ns ha y hy
      · exact Tm.fv_of_scoped l ns hl y hy

/-! ## Reading back -/

/-- **Name a de Bruijn term**: variables from `ns`, binders fresh. -/
def fromDB : List N → DeBruijn.Tm → Tm N
  | ns, .var i => .var (nameAt ns i)
  | _, .sort s => .sort s
  | ns, .pi A B => .pi (freshFor ns) (fromDB ns A) (fromDB (freshFor ns :: ns) B)
  | ns, .lam A t => .lam (freshFor ns) (fromDB ns A) (fromDB (freshFor ns :: ns) t)
  | ns, .app t u => .app (fromDB ns t) (fromDB ns u)
  | _, .ind i => .ind i
  | ns, .ctor i k m as => .ctor i k m (fromDB ns as)
  | ns, .elim i C bs t => .elim i (fromDB ns C) (fromDB ns bs) (fromDB ns t)
  | _, .tnil => .tnil
  | ns, .tcons a l => .tcons (fromDB ns a) (fromDB ns l)

/-- **Reading back and translating gives the term back**, for a scoped term and names without
repetitions. -/
theorem Tm.toDB_fromDB : ∀ (t : DeBruijn.Tm) (ns : List N), ns.Nodup → t.Scoped ns.length →
    (fromDB ns t).toDB ns = t
  | .var i, ns, hnd, h => by simp only [fromDB, Tm.toDB, lookupVar_nameAt hnd h]
  | .sort _, _, _, _ => rfl
  | .pi A B, ns, hnd, ⟨hA, hB⟩ => by
      have hnd' : (freshFor ns :: ns).Nodup := List.nodup_cons.mpr ⟨freshFor_not_in ns, hnd⟩
      simp only [fromDB, Tm.toDB, Tm.toDB_fromDB A ns hnd hA,
        Tm.toDB_fromDB B _ hnd' (by simpa using hB)]
  | .lam A t, ns, hnd, ⟨hA, ht⟩ => by
      have hnd' : (freshFor ns :: ns).Nodup := List.nodup_cons.mpr ⟨freshFor_not_in ns, hnd⟩
      simp only [fromDB, Tm.toDB, Tm.toDB_fromDB A ns hnd hA,
        Tm.toDB_fromDB t _ hnd' (by simpa using ht)]
  | .app t u, ns, hnd, ⟨ht, hu⟩ => by
      simp only [fromDB, Tm.toDB, Tm.toDB_fromDB t ns hnd ht, Tm.toDB_fromDB u ns hnd hu]
  | .ind _, _, _, _ => rfl
  | .ctor _ _ _ as, ns, hnd, h => by simp only [fromDB, Tm.toDB, Tm.toDB_fromDB as ns hnd h]
  | .elim _ C bs t, ns, hnd, ⟨hC, hbs, ht⟩ => by
      simp only [fromDB, Tm.toDB, Tm.toDB_fromDB C ns hnd hC, Tm.toDB_fromDB bs ns hnd hbs,
        Tm.toDB_fromDB t ns hnd ht]
  | .tnil, _, _, _ => rfl
  | .tcons a l, ns, hnd, ⟨ha, hl⟩ => by
      simp only [fromDB, Tm.toDB, Tm.toDB_fromDB a ns hnd ha, Tm.toDB_fromDB l ns hnd hl]

/-- A closed term translates the same against any binders. -/
theorem Tm.toDB_closed {t : Tm N} (h : t.fv = []) (ns : List N) : t.toDB ns = t.toDB [] := by
  rw [Tm.toDB_ren t [] ns id (fun x hx => by simp [h] at hx), DeBruijn.Tm.ren_id]

/-- Every scoped de Bruijn term is a translation. -/
theorem exists_toDB {X : DeBruijn.Tm} {ns : List N} (hnd : ns.Nodup) (h : X.Scoped ns.length) :
    ∃ A : Tm N, A.toDB ns = X :=
  ⟨_, Tm.toDB_fromDB X ns hnd h⟩

/-- Every closed de Bruijn term is a closed translation: the same against any binders. -/
theorem exists_closed {X : DeBruijn.Tm} (h : X.Scoped 0) : ∃ A : Tm N, ∀ ns, A.toDB ns = X := by
  have e := Tm.toDB_fromDB (N := N) X [] List.nodup_nil h
  have hfv : (fromDB [] X : Tm N).fv = [] := List.eq_nil_iff_forall_not_mem.mpr fun y hy => by
    simpa using Tm.fv_of_scoped (fromDB [] X) [] (by rw [e]; exact h) y hy
  exact ⟨fromDB [] X, fun ns => by rw [Tm.toDB_closed hfv ns, e]⟩

end LambdaLab.Languages.CoIC.Named
