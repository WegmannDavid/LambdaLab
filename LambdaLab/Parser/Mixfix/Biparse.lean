import LambdaLab.Parser.Biparser
import LambdaLab.Parser.Mixfix.Render
import LambdaLab.Parser.Mixfix.Parse
import LambdaLab.Parser.Mixfix.Verified

/-!
# Assembling the mixfix `Biparser`

`biparser` bundles the char-level prefix `parseChars` (tokenize + token parse) with
the policy-driven `renderExpr` into a `Biparser Char (Policy G) (Expr G e .loosest)`.
Both coherence laws are proved: `render_complete` from `cursor_render` (the cursor
policy reproduces the input), `parse_complete` from `char_parse_complete`
(`tokenize (renderExpr ex p) = ex.flatten` for every policy, plus membership in the
prefix parser). The biparser depends only on `propext`/`Classical.choice`/`Quot.sound`.
-/

namespace LambdaLab.Parser.Mixfix

open LambdaLab.Parser

/-! ## The `render_complete` witness (cursor policy)

The witness `State` is the **remaining input**. `traverse`/`traverseVar` read the
actual separator runs off it and advance past each rendered part, so rendering `ex`
reproduces the input verbatim. -/

/-- The leading run of separator characters of a char list, carrying the `isSep`
proofs. -/
def readSeps {G : Grammar} : List Char → List (Sep G)
  | []        => []
  | c :: rest => if h : G.isSep c = true then ⟨c, h⟩ :: readSeps rest else []

/-- Read the telescope tail off the remaining input: each gap is the actual
separator run there (promoted to `NESep` via the grammar's `sepWitness`); each
continuation drops the rendered part's chars. The `[]` case just returns the
remaining state — no right edge (trailing seps are the next token's gap, or
`trail`). -/
def cursorTail {G : Grammar} :
    List Char → (ps : List (Part G)) → LayoutTail G (List Char) ps
  | remaining, []      => remaining
  | remaining, _ :: ps =>
      let gap := readSeps remaining
      let remAfter := remaining.drop gap.length
      (mkNESep gap, remAfter, fun s _ => cursorTail s ps)

/-- Like `cursorTail`, but the first separator run is the (possibly-empty) left
edge. -/
def cursorLayout {G : Grammar} :
    List Char → (ps : List (Part G)) → Layout G (List Char) ps
  | remaining, []      => remaining
  | remaining, _ :: ps =>
      let edge := readSeps remaining
      let remAfter := remaining.drop edge.length
      (edge, remAfter, fun s _ => cursorTail s ps)

/-- The cursor witness policy: `State` is the remaining input. Each gap/leading run
is the actual `readSeps` there; the render threads the actual remaining input into
each continuation (`step` drops a token, a hole subtree returns its own leftover);
the global `trail` is whatever separators remain at the end. -/
def cursorPolicy {G : Grammar} (input : List Char) : Policy G where
  State       := List Char
  initial     := input
  step        := fun remaining t => remaining.drop t.val.toList.length
  traverse    := fun e o remaining => cursorLayout remaining (Operator.body e o)
  traverseVar := fun _ t remaining =>
    let leftEdge := readSeps remaining
    (leftEdge, (remaining.drop leftEdge.length).drop t.val.toList.length)
  trail       := fun remaining => readSeps remaining

/-! ### `readSeps` characterisation

`readSeps` is exactly `takeWhile isSep`, so advancing past it is `dropWhile isSep` —
the primitive the cursor render uses at every separator boundary. -/

theorem readSeps_map {G : Grammar} (l : List Char) :
    (readSeps (G := G) l).map (·.val) = l.takeWhile G.isSep := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    unfold readSeps
    split
    · rename_i hc; simp [hc, ih]
    · rename_i hc; simp [hc]

theorem readSeps_length {G : Grammar} (l : List Char) :
    (readSeps (G := G) l).length = (l.takeWhile G.isSep).length := by
  rw [← readSeps_map, List.length_map]

theorem readSeps_drop {G : Grammar} (l : List Char) :
    l.drop (readSeps (G := G) l).length = l.dropWhile G.isSep := by
  rw [readSeps_length]
  induction l with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : G.isSep c = true <;>
      simp [hc, List.drop_succ_cons, ih]

/-! ## Tokenizer-inverse + flat tokenize facts (Policy-independent: they only
mention `tokenize`, `readSeps`, `freBody`). -/

theorem mem_takeWhile_pred {α} (p : α → Bool) (l : List α) (c : α)
    (hc : c ∈ l.takeWhile p) : p c = true := by
  induction l with
  | nil => simp at hc
  | cons a as ih =>
    rw [List.takeWhile_cons] at hc; split at hc
    · rename_i hpa; rcases List.mem_cons.mp hc with h|h
      · subst h; exact hpa
      · exact ih h
    · simp at hc

theorem tokenizeAux_acc {sep : Char → Bool} (l : List Char) :
    ∀ (cur : List Char) (h : ∀ c ∈ cur, sep c = false)
      (hne : cur ++ l.takeWhile (fun c => !sep c) ≠ []),
    tokenizeAux sep cur h l =
      ⟨String.ofList (cur ++ l.takeWhile (fun c => !sep c)),
        (by intro c hc
            have hc' : c ∈ cur ++ l.takeWhile (fun c => !sep c) := by simpa using hc
            rcases List.mem_append.mp hc' with h1 | h2
            · exact h c h1
            · have := mem_takeWhile_pred _ _ _ h2; simpa using this),
        by simpa using hne⟩ ::
      tokenizeAux sep [] (by simp) (l.dropWhile (fun c => !sep c)) := by
  induction l with
  | nil =>
    intro cur h hne
    simp only [List.takeWhile_nil, List.append_nil] at hne ⊢
    simp only [tokenizeAux, List.dropWhile_nil, List.isEmpty_eq_false_iff.mpr hne,
      if_false, Bool.false_eq_true]
    rfl
  | cons c cs ih =>
    intro cur h hne
    by_cases hc : sep c = true
    · have hnsep : (!sep c) = false := by simp [hc]
      simp only [List.takeWhile_cons, hnsep, if_false, Bool.false_eq_true, List.append_nil,
        List.dropWhile_cons] at hne ⊢
      simp only [tokenizeAux, dif_pos hc, List.isEmpty_eq_false_iff.mpr hne, if_false,
        Bool.false_eq_true, List.singleton_append, List.isEmpty_nil, if_true, List.nil_append]
      rfl
    · have hnsep : (!sep c) = true := by simp [hc]
      have hcf : sep c = false := by simpa using hc
      simp only [List.takeWhile_cons, hnsep, if_true, List.dropWhile_cons] at hne ⊢
      simp only [tokenizeAux, dif_neg hc]
      have hne' : (cur ++ [c]) ++ cs.takeWhile (fun c => !sep c) ≠ [] := by simp
      rw [ih (cur ++ [c]) (by
            intro x hx; rcases List.mem_append.mp hx with h1|h1
            · exact h x h1
            · simp only [List.mem_singleton] at h1; subst h1; exact hcf) hne']
      simp only [List.append_assoc, List.singleton_append]

theorem dropWhile_head_neg {α} (p : α → Bool) (l : List α) (c : α) (cs : List α)
    (hh : l.dropWhile p = c :: cs) : p c = false := by
  induction l with
  | nil => simp at hh
  | cons a as ih =>
    rw [List.dropWhile_cons] at hh
    split at hh
    · exact ih hh
    · rename_i hpa; rw [List.cons.injEq] at hh; obtain ⟨rfl, _⟩ := hh; simpa using hpa

theorem tokenizeAux_dropWhile {sep : Char → Bool} (l : List Char)
    (h : ∀ c ∈ ([] : List Char), sep c = false) :
    tokenizeAux sep [] h l = tokenizeAux sep [] h (l.dropWhile sep) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : sep c = true
    · have : tokenizeAux sep [] h (c :: cs) = tokenizeAux sep [] h cs := by
        simp [tokenizeAux, hc]
      rw [this, ih, List.dropWhile_cons_of_pos hc]
    · rw [List.dropWhile_cons_of_neg (by simpa using hc)]

theorem tokenize_nil (G : Grammar) (input : List Char)
    (hnil : input.dropWhile G.isSep = []) : tokenize G input = [] := by
  unfold tokenize
  rw [tokenizeAux_dropWhile, hnil]
  simp [tokenizeAux]

theorem tokenize_cons (G : Grammar) (input : List Char) (c : Char) (cs : List Char)
    (hd : input.dropWhile G.isSep = c :: cs) :
    tokenize G input =
      ⟨String.ofList ((input.dropWhile G.isSep).takeWhile (fun c => !G.isSep c)),
        (by intro x hx; rw [String.toList_ofList] at hx
            have := mem_takeWhile_pred _ _ _ hx; simpa using this),
        (by have hic : G.isSep c = false := dropWhile_head_neg _ _ _ _ hd
            rw [String.toList_ofList, hd, List.takeWhile_cons]; simp [hic])⟩ ::
      tokenize G ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c)) := by
  unfold tokenize
  rw [tokenizeAux_dropWhile]
  have hisSepc : G.isSep c = false := dropWhile_head_neg _ _ _ _ hd
  have hne : ([] : List Char) ++ (input.dropWhile G.isSep).takeWhile (fun c => !G.isSep c) ≠ [] := by
    rw [hd]; simp [hisSepc]
  rw [tokenizeAux_acc (input.dropWhile G.isSep) [] (by simp) hne]
  simp only [List.nil_append]

theorem tokenize_sep_cons {G : Grammar} (c : Char) (cs : List Char) (hc : G.isSep c = true) :
    tokenize G (c :: cs) = tokenize G cs := by
  unfold tokenize
  simp [tokenizeAux, hc]

-- skipping a whole leading separator run

theorem tokenize_sep_prefix {G : Grammar} (run : List (Sep G)) (rest : List Char) :
    tokenize G (run.map (·.val) ++ rest) = tokenize G rest := by
  induction run with
  | nil => rfl
  | cons s run' ih =>
    simp only [List.map_cons, List.cons_append]
    rw [tokenize_sep_cons _ _ s.2, ih]

theorem takeWhile_append_all {α} (p : α → Bool) (a b : List α) (h : ∀ x ∈ a, p x = true) :
    (a ++ b).takeWhile p = a ++ b.takeWhile p := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.takeWhile_cons, if_pos (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]; rfl

theorem dropWhile_append_all {α} (p : α → Bool) (a b : List α) (h : ∀ x ∈ a, p x = true) :
    (a ++ b).dropWhile p = b.dropWhile p := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.dropWhile_cons, if_pos (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]

-- probe: does String.ofList_toList exist?

theorem dropWhile_of_takeWhile_nil {α} (p : α → Bool) (l : List α) (h : l.takeWhile p = []) :
    l.dropWhile p = l := by
  cases l with
  | nil => rfl
  | cons a as =>
    rw [List.takeWhile_cons] at h; split at h
    · simp at h
    · rename_i hn; exact List.dropWhile_cons_of_neg hn

theorem tokenize_token {G : Grammar} (t : Token G.isSep) (rest : List Char)
    (hrest : rest.takeWhile (fun c => !G.isSep c) = []) :
    tokenize G (t.val.toList ++ rest) = t :: tokenize G rest := by
  have hall : ∀ x ∈ t.val.toList, (fun c => !G.isSep c) x = true :=
    fun x hx => by simp [t.property.1 x hx]
  have htake : (t.val.toList ++ rest).takeWhile (fun c => !G.isSep c) = t.val.toList := by
    rw [takeWhile_append_all _ _ _ hall, hrest, List.append_nil]
  have hdrop : (t.val.toList ++ rest).dropWhile (fun c => !G.isSep c) = rest := by
    rw [dropWhile_append_all _ _ _ hall]; exact dropWhile_of_takeWhile_nil _ _ hrest
  have hne : ([] : List Char) ++ (t.val.toList ++ rest).takeWhile (fun c => !G.isSep c) ≠ [] := by
    rw [List.nil_append, htake]; exact t.property.2
  unfold tokenize
  rw [tokenizeAux_acc (t.val.toList ++ rest) [] (by simp) hne]
  congr 1
  · refine Subtype.ext ?_
    show String.ofList ([] ++ (t.val.toList ++ rest).takeWhile (fun c => !G.isSep c)) = t.val
    rw [List.nil_append, htake, String.ofList_toList]
  · rw [hdrop]

theorem takeWhile_append_nil {α} (p : α → Bool) (a b : List α)
    (ha : a.takeWhile p = []) (hb : b.takeWhile p = []) : (a ++ b).takeWhile p = [] := by
  cases a with
  | nil => simpa using hb
  | cons x xs =>
    rw [List.takeWhile_cons] at ha; split at ha
    · simp at ha
    · rename_i hn; rw [List.cons_append, List.takeWhile_cons, if_neg hn]

-- a renderSpTail output starts with its (nonempty) gap → a separator, so takeWhile-nsep is []

theorem length_dropWhile_le {α} (p : α → Bool) (l : List α) :
    (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.dropWhile_cons]; split
    · exact Nat.le_succ_of_le ih
    · simp

theorem drop_takeWhile_length {α} (p : α → Bool) (l : List α) :
    l.drop (l.takeWhile p).length = l.dropWhile p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases h : p a <;>
      simp [List.takeWhile_cons, List.dropWhile_cons, h, List.drop_succ_cons, ih]

def freBodyTail {G : Grammar} : List (Token G.isSep) → List Char → List Char × List Char
  | [],      rem => ([], rem)
  | t :: ts, rem =>
      let run := readSeps (G := G) rem
      let res := freBodyTail ts ((rem.drop run.length).drop t.val.toList.length)
      ((mkNESep run).toList.map (·.val) ++ t.val.toList ++ res.1, res.2)

def freBody {G : Grammar} : List (Token G.isSep) → List Char → List Char × List Char
  | [],      rem => ([], rem)
  | t :: ts, rem =>
      let run := readSeps (G := G) rem
      let res := freBodyTail ts ((rem.drop run.length).drop t.val.toList.length)
      (run.map (·.val) ++ t.val.toList ++ res.1, res.2)

def freBodyReassemble {G : Grammar} (toks : List (Token G.isSep)) (x : List Char) : List Char :=
  (freBody toks x).1 ++ (readSeps (G := G) (freBody toks x).2).map (·.val)

theorem freBodyTail_eq_freBody {G : Grammar} (toks : List (Token G.isSep)) (rem : List Char)
    (h : toks = [] ∨ readSeps (G := G) rem ≠ []) :
    freBodyTail toks rem = freBody toks rem := by
  cases toks with
  | nil => rfl
  | cons t ts =>
    have hne : readSeps (G := G) rem ≠ [] := h.resolve_left (by simp)
    simp only [freBodyTail, freBody, mkNESep_toList_of_ne hne]

theorem freBody_tokenize (G : Grammar) : ∀ (n : Nat) (input : List Char),
    input.length ≤ n → freBodyReassemble (tokenize G input) input = input := by
  intro n
  induction n with
  | zero =>
    intro input hlen
    have : input = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst this
    simp [freBodyReassemble, freBody, readSeps, tokenize_nil G [] rfl]
  | succ n ih =>
    intro input hlen
    cases hd : input.dropWhile G.isSep with
    | nil =>
      rw [tokenize_nil G input hd]
      simp only [freBodyReassemble, freBody, List.nil_append]
      rw [readSeps_map]
      have : input.takeWhile G.isSep ++ input.dropWhile G.isSep = input :=
        List.takeWhile_append_dropWhile
      rw [hd, List.append_nil] at this
      exact this
    | cons c cs =>
      rw [tokenize_cons G input c cs hd]
      have hisc : G.isSep c = false := dropWhile_head_neg _ _ _ _ hd
      have hcs : cs.length + 1 ≤ input.length := by
        have hle := length_dropWhile_le G.isSep input
        rw [hd] at hle; simpa using hle
      have hrestlen : ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c)).length ≤ n := by
        rw [hd, List.dropWhile_cons_of_pos (by simp [hisc])]
        have := length_dropWhile_le (fun c => !G.isSep c) cs
        omega
      have hIH := ih ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c)) hrestlen
      simp only [freBodyReassemble] at hIH
      have hconv : freBodyTail (tokenize G ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c)))
                     ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c))
                 = freBody (tokenize G ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c)))
                     ((input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c)) := by
        apply freBodyTail_eq_freBody
        cases hr : (input.dropWhile G.isSep).dropWhile (fun c => !G.isSep c) with
        | nil => left; exact tokenize_nil G [] rfl
        | cons d ds =>
          right
          have hsd : G.isSep d = true := by
            have := dropWhile_head_neg (fun c => !G.isSep c) (input.dropWhile G.isSep) d ds hr
            simpa using this
          simp [readSeps, hsd]
      simp only [freBodyReassemble, freBody, String.toList_ofList, readSeps_drop,
        drop_takeWhile_length]
      rw [hconv, List.append_assoc, hIH, readSeps_map, List.append_assoc,
        List.takeWhile_append_dropWhile, List.takeWhile_append_dropWhile]

theorem readSeps_dropWhile {G : Grammar} (l : List Char) :
    readSeps (G := G) (l.dropWhile G.isSep) = [] := by
  cases hd : l.dropWhile G.isSep with
  | nil => rfl
  | cons c rest => have hc : G.isSep c = false := dropWhile_head_neg _ _ _ _ hd; simp [readSeps, hc]

theorem freBodyTail_append {G : Grammar} (toks1 toks2 : List (Token G.isSep)) (rem : List Char) :
    freBodyTail (toks1 ++ toks2) rem =
      ((freBodyTail toks1 rem).1 ++ (freBodyTail toks2 (freBodyTail toks1 rem).2).1,
       (freBodyTail toks2 (freBodyTail toks1 rem).2).2) := by
  induction toks1 generalizing rem with
  | nil => simp [freBodyTail]
  | cons t ts ih => simp only [List.cons_append, freBodyTail, ih, List.append_assoc]

theorem freBody_append {G : Grammar} (toks1 toks2 : List (Token G.isSep)) (rem : List Char)
    (h : toks1 ≠ []) :
    freBody (toks1 ++ toks2) rem =
      ((freBody toks1 rem).1 ++ (freBodyTail toks2 (freBody toks1 rem).2).1,
       (freBodyTail toks2 (freBody toks1 rem).2).2) := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [List.cons_append, freBody, freBodyTail_append, List.append_assoc]

theorem freBodyTail_lead {G : Grammar} (t : Token G.isSep) (ts : List (Token G.isSep))
    (state : List Char)
    (hs0 : readSeps (G := G) (state.drop (readSeps (G := G) state).length) = []) :
    freBodyTail (t :: ts) state =
      ((mkNESep (readSeps (G := G) state)).toList.map (·.val) ++
        (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).1,
       (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).2) := by
  simp only [freBodyTail, freBody, hs0, List.length_nil, List.drop_zero, List.map_nil,
    List.nil_append, List.append_assoc]

theorem freBody_lead {G : Grammar} (t : Token G.isSep) (ts : List (Token G.isSep)) (state : List Char)
    (hs0 : readSeps (G := G) (state.drop (readSeps (G := G) state).length) = []) :
    freBody (t :: ts) state =
      ((readSeps (G := G) state).map (·.val) ++
        (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).1,
       (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).2) := by
  simp only [freBody, hs0, List.length_nil, List.drop_zero, List.map_nil, List.nil_append,
    List.append_assoc]

theorem freBodyReassemble_lead {G : Grammar} (toks : List (Token G.isSep)) (input : List Char) :
    freBodyReassemble toks input =
      (readSeps (G := G) input).map (·.val) ++
      freBodyReassemble toks (input.drop (readSeps (G := G) input).length) := by
  have hs0 : readSeps (G := G) (input.drop (readSeps (G := G) input).length) = [] := by
    rw [readSeps_drop]; exact readSeps_dropWhile input
  cases toks with
  | nil => simp [freBodyReassemble, freBody, hs0]
  | cons t ts =>
    simp only [freBodyReassemble, freBody, hs0, List.length_nil, List.drop_zero,
      List.map_nil, List.nil_append, List.append_assoc]

/-! ### Cursor-render reduction lemmas

Each unfolds one step of `Expr.render`/`Parts.render`/`Parts.renderTail` **under the
cursor policy specifically** — keeping `cursorLayout`/`cursorTail` folded rather than
destructured, so `rw` can fire them (the generic `Parts.render.eq_*` equations do not,
because the token appears in a type index of the dependent match). All hold by `rfl`. -/
theorem rE_op {G : Grammar} (input : List Char) {e : G.Ent} {l : Level (G.entry e)}
    (o : (G.entry e).Op) (cond : Level.condition l o)
    (parts : Parts G (Operator.body e o)) (state : List Char) :
    Expr.render (cursorPolicy input) state e (.op o cond parts)
    = Parts.render (cursorPolicy input) (Operator.body e o) (cursorLayout state (Operator.body e o)) parts := rfl
theorem rE_var {G : Grammar} (input : List Char) {e : G.Ent} {l : Level (G.entry e)}
    (t : Token G.isSep) (hv : (G.entry e).isVar t = true) (state : List Char) :
    Expr.render (cursorPolicy input) state e (.var (l := l) t hv)
    = ((readSeps (G := G) state).map (·.val) ++ t.val.toList,
       (state.drop (readSeps (G := G) state).length).drop t.val.toList.length) := rfl
theorem rP_nil {G : Grammar} (input : List Char) (state : List Char) :
    Parts.render (cursorPolicy input) ([] : List (Part G)) (cursorLayout state []) .nil = ([], state) := rfl
theorem rP_namePart {G : Grammar} (input : List Char) {ps : List (Part G)}
    (tk : Token G.isSep) (rest : Parts G ps) (state : List Char) :
    Parts.render (cursorPolicy input) (.namePart tk :: ps) (cursorLayout state (.namePart tk :: ps)) (.namePart tk rest)
    = ((readSeps (G := G) state).map (·.val) ++ tk.val.toList
        ++ (Parts.renderTail (cursorPolicy input) ps (cursorTail ((state.drop (readSeps (G := G) state).length).drop tk.val.toList.length) ps) rest).1,
       (Parts.renderTail (cursorPolicy input) ps (cursorTail ((state.drop (readSeps (G := G) state).length).drop tk.val.toList.length) ps) rest).2) := rfl
theorem rP_hole {G : Grammar} (input : List Char) {e' : G.Ent} {l' : Level (G.entry e')}
    {ps : List (Part G)} (ex' : Expr G e' l') (rest : Parts G ps) (state : List Char) :
    Parts.render (cursorPolicy input) (.hole e' l' :: ps) (cursorLayout state (.hole e' l' :: ps)) (.hole ex' rest)
    = ((readSeps (G := G) state).map (·.val)
        ++ (Expr.render (cursorPolicy input) (state.drop (readSeps (G := G) state).length) e' ex').1
        ++ (Parts.renderTail (cursorPolicy input) ps (cursorTail (Expr.render (cursorPolicy input) (state.drop (readSeps (G := G) state).length) e' ex').2 ps) rest).1,
       (Parts.renderTail (cursorPolicy input) ps (cursorTail (Expr.render (cursorPolicy input) (state.drop (readSeps (G := G) state).length) e' ex').2 ps) rest).2) := rfl
theorem rT_nil {G : Grammar} (input : List Char) (state : List Char) :
    Parts.renderTail (cursorPolicy input) ([] : List (Part G)) (cursorTail state []) .nil = ([], state) := rfl
theorem rT_namePart {G : Grammar} (input : List Char) {ps : List (Part G)}
    (tk : Token G.isSep) (rest : Parts G ps) (state : List Char) :
    Parts.renderTail (cursorPolicy input) (.namePart tk :: ps) (cursorTail state (.namePart tk :: ps)) (.namePart tk rest)
    = ((mkNESep (readSeps (G := G) state)).toChars ++ tk.val.toList
        ++ (Parts.renderTail (cursorPolicy input) ps (cursorTail ((state.drop (readSeps (G := G) state).length).drop tk.val.toList.length) ps) rest).1,
       (Parts.renderTail (cursorPolicy input) ps (cursorTail ((state.drop (readSeps (G := G) state).length).drop tk.val.toList.length) ps) rest).2) := rfl
theorem rT_hole {G : Grammar} (input : List Char) {e' : G.Ent} {l' : Level (G.entry e')}
    {ps : List (Part G)} (ex' : Expr G e' l') (rest : Parts G ps) (state : List Char) :
    Parts.renderTail (cursorPolicy input) (.hole e' l' :: ps) (cursorTail state (.hole e' l' :: ps)) (.hole ex' rest)
    = ((mkNESep (readSeps (G := G) state)).toChars
        ++ (Expr.render (cursorPolicy input) (state.drop (readSeps (G := G) state).length) e' ex').1
        ++ (Parts.renderTail (cursorPolicy input) ps (cursorTail (Expr.render (cursorPolicy input) (state.drop (readSeps (G := G) state).length) e' ex').2 ps) rest).1,
       (Parts.renderTail (cursorPolicy input) ps (cursorTail (Expr.render (cursorPolicy input) (state.drop (readSeps (G := G) state).length) e' ex').2 ps) rest).2) := rfl

/-! Every `Expr` flattens to a **nonempty** token list — needed so the hole cases below
can pull the leading separator run out of a subtree's first token (`freBody_lead`). -/
mutual
theorem Expr.flatten_ne_nil {G : Grammar} {e : G.Ent} {l : Level (G.entry e)}
    (ex : Expr G e l) : ex.flatten ≠ [] :=
  match ex with
  | .op o _ parts => by simp only [Expr.flatten]; exact Parts.flatten_ne_nil parts (Operator.body_ne_nil o)
  | .var t _ => by simp [Expr.flatten]
theorem Parts.flatten_ne_nil {G : Grammar} {shape : List (Part G)}
    (parts : Parts G shape) (hne : shape ≠ []) : parts.flatten ≠ [] :=
  match parts with
  | .nil => absurd rfl hne
  | .namePart tk rest => by simp [Parts.flatten]
  | .hole ex rest => by simp only [Parts.flatten]; exact List.append_ne_nil_of_left_ne_nil (Expr.flatten_ne_nil ex) _
end

/-- After dropping a maximal separator run there is no separator left to read. -/
theorem hs0_of {G : Grammar} (state : List Char) :
    readSeps (G := G) (state.drop (readSeps (G := G) state).length) = [] := by
  rw [readSeps_drop]; exact readSeps_dropWhile state

/-- `freBody_lead` for a nonempty (rather than explicitly `cons`) token list. -/
theorem freBody_lead_ne {G : Grammar} (toks : List (Token G.isSep)) (state : List Char)
    (hne : toks ≠ []) (hs0 : readSeps (G := G) (state.drop (readSeps (G := G) state).length) = []) :
    freBody toks state =
      ((readSeps (G := G) state).map (·.val) ++ (freBody toks (state.drop (readSeps (G := G) state).length)).1,
       (freBody toks (state.drop (readSeps (G := G) state).length)).2) := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil hne; exact freBody_lead t ts state hs0

/-- `freBodyTail_lead` for a nonempty (rather than explicitly `cons`) token list. -/
theorem freBodyTail_lead_ne {G : Grammar} (toks : List (Token G.isSep)) (state : List Char)
    (hne : toks ≠ []) (hs0 : readSeps (G := G) (state.drop (readSeps (G := G) state).length) = []) :
    freBodyTail toks state =
      ((mkNESep (readSeps (G := G) state)).toList.map (·.val) ++ (freBody toks (state.drop (readSeps (G := G) state).length)).1,
       (freBody toks (state.drop (readSeps (G := G) state).length)).2) := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil hne; exact freBodyTail_lead t ts state hs0

/-! **The lockstep lemma**: rendering a subtree under `cursorPolicy input` from `state`
reproduces exactly the `freBody` reassembly of its flattened tokens over `state` — the
cursor consumes `state` in the same order the tokenizer laid it down. State is threaded
by *actual consumption* (`step` for tokens, the subtree's returned remainder for holes),
so no validity hypothesis on `state` is needed; the leading-run bookkeeping is discharged
by `freBody_append`/`freBody_lead` in the hole cases. -/
mutual
theorem render_expr {G : Grammar} (input : List Char) {e : G.Ent} {l : Level (G.entry e)}
    (ex : Expr G e l) (state : List Char) :
    Expr.render (cursorPolicy input) state e ex = freBody ex.flatten state :=
  match ex with
  | .op o _ parts => by rw [rE_op]; exact render_parts input parts state
  | .var t hv => by rw [rE_var]; simp [Expr.flatten, freBody, freBodyTail]
theorem render_parts {G : Grammar} (input : List Char) {ps : List (Part G)}
    (parts : Parts G ps) (state : List Char) :
    Parts.render (cursorPolicy input) ps (cursorLayout state ps) parts = freBody parts.flatten state :=
  match parts with
  | .nil => by rw [rP_nil]; rfl
  | .namePart tk rest => by rw [rP_namePart, render_tail input rest]; rfl
  | .hole ex' rest => by
      rw [rP_hole, render_expr input ex' _, render_tail input rest, Parts.flatten,
          freBody_append _ _ _ (Expr.flatten_ne_nil ex'),
          freBody_lead_ne _ state (Expr.flatten_ne_nil ex') (hs0_of state)]
      simp only [List.append_assoc]; rfl
theorem render_tail {G : Grammar} (input : List Char) {ps : List (Part G)}
    (parts : Parts G ps) (state : List Char) :
    Parts.renderTail (cursorPolicy input) ps (cursorTail state ps) parts = freBodyTail parts.flatten state :=
  match parts with
  | .nil => by rw [rT_nil]; rfl
  | .namePart tk rest => by rw [rT_namePart, render_tail input rest]; rfl
  | .hole ex' rest => by
      rw [rT_hole, render_expr input ex' _, render_tail input rest, Parts.flatten,
          freBodyTail_append, freBodyTail_lead_ne _ state (Expr.flatten_ne_nil ex') (hs0_of state)]
      simp only [List.append_assoc, NESep.toChars, NESep.toList, List.map_cons]; rfl
end

theorem cP_initial {G : Grammar} (input : List Char) : (cursorPolicy (G := G) input).initial = input := rfl
theorem cP_trail {G : Grammar} (input : List Char) :
    (cursorPolicy (G := G) input).trail = fun r => readSeps (G := G) r := rfl

/-- Under the cursor policy, top-level `renderExpr` is exactly the `freBody`
reassembly of the tree's flattened tokens over the whole input. -/
theorem render_eq_freBodyReassemble {G : Grammar} (input : List Char) {e : G.Ent}
    (ex : Expr G e .loosest) :
    renderExpr ex (cursorPolicy input) = freBodyReassemble ex.flatten input := by
  simp only [renderExpr, cP_initial, cP_trail, render_expr input ex input, freBodyReassemble]

/-- **Heart of `render_complete`**: the cursor witness reproduces the input. `renderExpr`
under `cursorPolicy` is the `freBody` reassembly of the tree's tokens
(`render_eq_freBodyReassemble`); those tokens are `tokenize G input` (`parse_sound`); and
reassembling a tokenization is the identity (`freBody_tokenize`). -/
theorem cursor_render {G : Grammar} (input : List Char)
    {e : G.Ent} (ex : Expr G e .loosest) (h : ex ∈ parse e (tokenize G input)) :
    renderExpr ex (cursorPolicy input) = input := by
  rw [render_eq_freBodyReassemble, parse_sound h]
  exact freBody_tokenize G input.length input (Nat.le_refl _)

/-! ### `parse_complete`: `tokenize (renderExpr ex p) = ex.flatten`, then membership
in the prefix parser.

The render half above only needed the *cursor* policy; `parse_complete` must hold for
**every** policy `p`, so it goes through `tokenize (renderExpr ex p) = ex.flatten`. The
key is that a rendered gap is always a nonempty separator run (`NESep`) and tokens are
nonempty and separator-free, so re-tokenizing a rendering recovers exactly the flattened
tokens — no two tokens ever merge. -/

/-- General (policy-agnostic) one-step reductions of `Parts.render`/`Parts.renderTail`,
holding by `rfl` with the layout kept as an explicit tuple (so `simp`/`rw` can fire them
past the dependent match). -/
theorem render_namePart_eq {G : Grammar} (policy : Policy G) {ps : List (Part G)}
    (leftEdge : List (Sep G)) (st : policy.State) (k : policy.State → List Char → LayoutTail G policy.State ps)
    (tk : Token G.isSep) (rest : Parts G ps) :
    Parts.render policy (.namePart tk :: ps) (leftEdge, st, k) (.namePart tk rest)
    = (leftEdge.map (·.val) ++ tk.val.toList ++ (Parts.renderTail policy ps (k (policy.step st tk) tk.val.toList) rest).1,
       (Parts.renderTail policy ps (k (policy.step st tk) tk.val.toList) rest).2) := rfl
theorem render_hole_eq {G : Grammar} (policy : Policy G) {e' : G.Ent} {l' : Level (G.entry e')}
    {ps : List (Part G)} (leftEdge : List (Sep G)) (st : policy.State)
    (k : policy.State → List Char → LayoutTail G policy.State ps) (ex' : Expr G e' l') (rest : Parts G ps) :
    Parts.render policy (.hole e' l' :: ps) (leftEdge, st, k) (.hole ex' rest)
    = (leftEdge.map (·.val) ++ (Expr.render policy st e' ex').1
        ++ (Parts.renderTail policy ps (k (Expr.render policy st e' ex').2 (Expr.render policy st e' ex').1) rest).1,
       (Parts.renderTail policy ps (k (Expr.render policy st e' ex').2 (Expr.render policy st e' ex').1) rest).2) := rfl
theorem renderTail_namePart_eq {G : Grammar} (policy : Policy G) {ps : List (Part G)}
    (gap : NESep G) (st : policy.State) (k : policy.State → List Char → LayoutTail G policy.State ps)
    (tk : Token G.isSep) (rest : Parts G ps) :
    Parts.renderTail policy (.namePart tk :: ps) (gap, st, k) (.namePart tk rest)
    = (gap.toChars ++ tk.val.toList ++ (Parts.renderTail policy ps (k (policy.step st tk) tk.val.toList) rest).1,
       (Parts.renderTail policy ps (k (policy.step st tk) tk.val.toList) rest).2) := rfl
theorem renderTail_hole_eq {G : Grammar} (policy : Policy G) {e' : G.Ent} {l' : Level (G.entry e')}
    {ps : List (Part G)} (gap : NESep G) (st : policy.State)
    (k : policy.State → List Char → LayoutTail G policy.State ps) (ex' : Expr G e' l') (rest : Parts G ps) :
    Parts.renderTail policy (.hole e' l' :: ps) (gap, st, k) (.hole ex' rest)
    = (gap.toChars ++ (Expr.render policy st e' ex').1
        ++ (Parts.renderTail policy ps (k (Expr.render policy st e' ex').2 (Expr.render policy st e' ex').1) rest).1,
       (Parts.renderTail policy ps (k (Expr.render policy st e' ex').2 (Expr.render policy st e' ex').1) rest).2) := rfl
theorem render_nil_eq {G : Grammar} (policy : Policy G) (st : Layout G policy.State []) :
    Parts.render policy [] st Parts.nil = ([], st) := rfl
theorem renderTail_nil_eq {G : Grammar} (policy : Policy G) (st : LayoutTail G policy.State []) :
    Parts.renderTail policy [] st Parts.nil = ([], st) := rfl

/-- A separator run's chars are just its list-of-separators mapped to chars. -/
theorem NESep.toChars_eq_map {G : Grammar} (s : NESep G) : s.toChars = s.toList.map (·.val) := rfl

/-- A `renderTail` fragment starts with its (nonempty) gap — a separator — so nothing
non-separator leads it; used to satisfy `tokenize_token`'s "suffix starts with a
separator" side condition at every part boundary. -/
theorem renderTail_head_sep {G : Grammar} (policy : Policy G) {ps : List (Part G)}
    (tail : LayoutTail G policy.State ps) (parts : Parts G ps) :
    (Parts.renderTail policy ps tail parts).1.takeWhile (fun c => !G.isSep c) = [] := by
  cases parts with
  | nil => rfl
  | namePart tk rest =>
      obtain ⟨gap, st, k⟩ := tail
      rw [renderTail_namePart_eq, NESep.toChars]
      simp [List.takeWhile_cons, gap.head.2]
  | hole ex' rest =>
      obtain ⟨gap, st, k⟩ := tail
      rw [renderTail_hole_eq, NESep.toChars]
      simp [List.takeWhile_cons, gap.head.2]

/-- **The tokenizer-inverse invariant**: for any policy, rendering a subtree then
tokenizing (with any separator-led `suffix` appended) recovers the subtree's flattened
tokens followed by the tokenization of `suffix`. Every internal gap is `NESep`
(nonempty) and every token is nonempty/sep-free, so no boundary merge occurs. Proved by
the render recursion (`Expr.render.induct`) — the arbitrary layouts are fine because
their edges are typed `Sep`/`NESep`, hence always separators. -/
theorem tokenize_render_INV {G : Grammar} (policy : Policy G) :
    ∀ (state : policy.State) (e : G.Ent) {l : Level (G.entry e)} (ex : Expr G e l) (suffix : List Char),
      suffix.takeWhile (fun c => !G.isSep c) = [] →
      tokenize G ((Expr.render policy state e ex).1 ++ suffix) = ex.flatten ++ tokenize G suffix := by
  apply Expr.render.induct (policy := policy)
    (motive_2 := fun ps lay parts => ∀ (suffix : List Char),
      suffix.takeWhile (fun c => !G.isSep c) = [] →
      tokenize G ((Parts.render policy ps lay parts).1 ++ suffix) = parts.flatten ++ tokenize G suffix)
    (motive_3 := fun ps tail parts => ∀ (suffix : List Char),
      suffix.takeWhile (fun c => !G.isSep c) = [] →
      tokenize G ((Parts.renderTail policy ps tail parts).1 ++ suffix) = parts.flatten ++ tokenize G suffix)
  · -- op
    intro e a state o cond parts ih suffix hsuf
    simpa [Expr.render, Expr.flatten] using ih suffix hsuf
  · -- var
    intro e a state t hvar leftEdge state' heq suffix hsuf
    simp only [Expr.render, heq, Expr.flatten]
    rw [List.append_assoc, tokenize_sep_prefix, tokenize_token t suffix hsuf, List.singleton_append]
  · -- Parts.render nil
    intro st t suffix hsuf
    cases t; rw [render_nil_eq]; simp [Parts.flatten]
  · -- Parts.render namePart
    intro tk psTail leftEdge st k prest r rest st' heq_rt m3 suffix hsuf
    have er : r = tk.val.toList := rfl
    rw [er] at heq_rt m3
    have h1 : rest.takeWhile (fun c => !G.isSep c) = [] := by
      have := renderTail_head_sep policy (k (policy.step st tk) tk.val.toList) prest
      rw [heq_rt] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) rest suffix h1 hsuf
    have hm3 := m3 suffix hsuf; rw [heq_rt] at hm3
    simp only [render_namePart_eq, heq_rt, Parts.flatten, List.append_assoc]
    rw [tokenize_sep_prefix, tokenize_token tk _ hcond, hm3, List.cons_append]
  · -- Parts.render hole
    intro e' a psTail leftEdge st k ex prest rest st' heq_r rest1 st'1 heq_rt m1 m3 suffix hsuf
    have h2 : rest1.takeWhile (fun c => !G.isSep c) = [] := by
      have := renderTail_head_sep policy (k st' rest) prest
      rw [heq_rt] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) rest1 suffix h2 hsuf
    have hm1 := m1 (rest1 ++ suffix) hcond; rw [heq_r] at hm1
    have hm3 := m3 suffix hsuf; rw [heq_rt] at hm3
    simp only [render_hole_eq, heq_r, heq_rt, Parts.flatten, List.append_assoc]
    rw [tokenize_sep_prefix, hm1, hm3]
  · -- Parts.renderTail nil
    intro st t suffix hsuf
    cases t; rw [renderTail_nil_eq]; simp [Parts.flatten]
  · -- Parts.renderTail namePart
    intro tk psTail gap st k prest r rest st' heq_rt m3 suffix hsuf
    have er : r = tk.val.toList := rfl
    rw [er] at heq_rt m3
    have h1 : rest.takeWhile (fun c => !G.isSep c) = [] := by
      have := renderTail_head_sep policy (k (policy.step st tk) tk.val.toList) prest
      rw [heq_rt] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) rest suffix h1 hsuf
    have hm3 := m3 suffix hsuf; rw [heq_rt] at hm3
    simp only [renderTail_namePart_eq, heq_rt, Parts.flatten, NESep.toChars_eq_map, List.append_assoc]
    rw [tokenize_sep_prefix, tokenize_token tk _ hcond, hm3, List.cons_append]
  · -- Parts.renderTail hole
    intro e' a psTail gap st k ex prest rest st' heq_r rest1 st'1 heq_rt m1 m3 suffix hsuf
    have h2 : rest1.takeWhile (fun c => !G.isSep c) = [] := by
      have := renderTail_head_sep policy (k st' rest) prest
      rw [heq_rt] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) rest1 suffix h2 hsuf
    have hm1 := m1 (rest1 ++ suffix) hcond; rw [heq_r] at hm1
    have hm3 := m3 suffix hsuf; rw [heq_rt] at hm3
    simp only [renderTail_hole_eq, heq_r, heq_rt, Parts.flatten, NESep.toChars_eq_map, List.append_assoc]
    rw [tokenize_sep_prefix, hm1, hm3]

/-- A trailing/leading separator run tokenizes away (its chars are all separators). -/
theorem sepRun_takeWhile_nil {G : Grammar} (run : List (Sep G)) :
    (run.map (·.val)).takeWhile (fun c => !G.isSep c) = [] := by
  cases run with
  | nil => rfl
  | cons s run' => simp [List.map_cons, List.takeWhile_cons, s.2]

/-- **Re-tokenizing a rendering recovers the flattened tokens**, for *any* policy. -/
theorem tokenize_renderExpr {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (p : Policy G) :
    tokenize G (renderExpr ex p) = ex.flatten := by
  simp only [renderExpr]
  rw [tokenize_render_INV p _ _ ex _ (sepRun_takeWhile_nil _)]
  rw [show (p.trail (Expr.render p p.initial e ex).2).map (·.val)
        = ((p.trail (Expr.render p p.initial e ex).2).map (·.val)) ++ [] from (List.append_nil _).symm,
     tokenize_sep_prefix, tokenize_nil G [] rfl, List.append_nil]

/-- Membership in the prefix `parseChars`: a token-level parse of the `n+1`-char prefix
lifts to a char-level parse leaving the rest. -/
theorem mem_parseChars {G : Grammar} {e : G.Ent} {input : List Char} {n : Nat}
    {ex : Expr G e .loosest} (hn : n < input.length)
    (hex : ex ∈ parse e (tokenize G (input.take (n + 1)))) :
    (ex, (⟨input.drop (n + 1), input.take (n + 1),
      by cases input with | nil => simp at hn | cons c cs => simp [List.take_succ_cons],
      List.take_append_drop (n + 1) input⟩ : RightSublist input)) ∈ parseChars e input := by
  cases input with
  | nil => simp at hn
  | cons c cs =>
    simp only [parseChars, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨n, hn, ex, hex, rfl⟩

/-- **Parser completeness / renderer soundness** for the char biparser: every rendering
`renderExpr ex p` (then any `rest`) parses back to `ex`, leaving exactly `rest`. -/
theorem char_parse_complete {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (p : Policy G)
    (rest : List Char) :
    ∃ s : RightSublist (renderExpr ex p ++ rest),
      s.list = rest ∧ (ex, s) ∈ parseChars e (renderExpr ex p ++ rest) := by
  have htok : tokenize G (renderExpr ex p) = ex.flatten := tokenize_renderExpr ex p
  have hne : renderExpr ex p ≠ [] := fun h =>
    Expr.flatten_ne_nil ex (by rw [← htok, h]; exact tokenize_nil G [] rfl)
  have hpos : 0 < (renderExpr ex p).length := List.length_pos_iff.mpr hne
  have hlt : (renderExpr ex p).length - 1 < (renderExpr ex p ++ rest).length := by
    rw [List.length_append]; omega
  have hex : ex ∈ parse e
      (tokenize G ((renderExpr ex p ++ rest).take ((renderExpr ex p).length - 1 + 1))) := by
    rw [Nat.sub_add_cancel hpos, List.take_left, htok]; exact parse_complete ex
  refine ⟨_, ?_, mem_parseChars hlt hex⟩
  show (renderExpr ex p ++ rest).drop ((renderExpr ex p).length - 1 + 1) = rest
  rw [Nat.sub_add_cancel hpos, List.drop_left]

/-- The mixfix biparser at start entry `e`: parse chars into a loosest tree, render
a tree back to chars under a `Policy G`. Both coherence laws are now proved —
`render_complete` from `cursor_render`, `parse_complete` from `char_parse_complete`. -/
def biparser {G : Grammar} {e : G.Ent} : Biparser Char (Policy G) (Expr G e .loosest) where
  render          := renderExpr
  parse           := parseChars e
  render_complete := by
    intro input ex s hmem
    cases input with
    | nil => simp [parseChars] at hmem
    | cons c cs =>
      simp only [parseChars, List.mem_flatMap, List.mem_map, List.mem_range] at hmem
      obtain ⟨n, hn, ex', hex', heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ heq
      -- Witness is the cursor policy at the consumed prefix; the equation is `cursor_render`.
      exact ⟨cursorPolicy ((c :: cs).take (n + 1)),
        cursor_render ((c :: cs).take (n + 1)) ex' hex'⟩
  parse_complete := char_parse_complete

/-- The **token-level** mixfix biparser: `parse` is the precedence parser, `render`
is `flatten`, and there is nothing to choose (`Policy := Unit`). Both laws hold
outright — `render_complete` is `parseExpr_sound`, `parse_complete` is
`parseExpr_complete`. This is the verified core; a char-level biparser is this
composed with a tokenizer. -/
def tokenBiparser {G : Grammar} {e : G.Ent} : Biparser (Token G.isSep) Unit (Expr G e .loosest) where
  render          := fun ex _ => ex.flatten
  parse           := fun tkns => parseExpr e .loosest tkns
  render_complete := by
    intro input ex s hmem
    refine ⟨(), ?_⟩
    show ex.flatten = s.pre
    have hsound : ex.flatten ++ s.list = input := parseExpr_sound (x := (ex, s)) hmem
    have h : ex.flatten ++ s.list = s.pre ++ s.list := hsound.trans s.eq.symm
    have hlen : ex.flatten.length = s.pre.length := by
      have hl := congrArg List.length h
      simp [List.length_append] at hl
      omega
    exact (List.append_inj h hlen).1
  parse_complete := by
    intro ex _ rest
    exact parseExpr_complete ex (ex.flatten ++ rest) rest rfl

end LambdaLab.Parser.Mixfix
