import LambdaLab.Parser2.Mixfix.Render
import LambdaLab.Parser2.Mixfix.Parse
import LambdaLab.Parser2.Mixfix.Verified

/-!
# Assembling the mixfix `Biparser` (split render)

`renderExpr` factors as (tree layout → spaced token list) then (flat join). So the
`render_complete` witness is a **cursor policy** whose threaded `State` is the
remaining input: `lead`/`gap` read the actual separator run off it (`readSeps`) and
`step` drops the rendered token — so rendering reproduces the input. Gaps are typed
`NESep G` (nonempty), so every render separates its tokens and `parse_complete`
holds unconditionally; the witness promotes an empty run with `mkNESep`, whose
fallback is the grammar's canonical `sepWitness` — so no threaded default (`dflt`)
is needed. `render_complete` reduces to `cursor_render` alone.
-/

namespace LambdaLab.Parser2.Mixfix

open LambdaLab.Parser2

/-! ## `readSeps`: the leading separator run, with proofs -/

/-- The leading run of separator characters, carrying the `isSep` proofs. -/
def readSeps {G : Grammar} : List Char → List (Sep G)
  | []        => []
  | c :: rest => if h : G.isSep c = true then ⟨c, h⟩ :: readSeps rest else []

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

/-! ## Tokenizer characterisation

The flat "tokenizer-inverse": `tokenize` splits off leading separators then a maximal
non-separator run, and re-interleaving the tokens with the separator runs
(`freBodyReassemble`) recovers the input exactly. -/

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

/-- The accumulator-flush characterisation of `tokenizeAux`: it emits the current
accumulator plus the next non-separator run as one token, then recurses. -/
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

/-- The head of a `dropWhile p` fails `p`. -/
theorem dropWhile_head_neg {α} (p : α → Bool) (l : List α) (c : α) (cs : List α)
    (hh : l.dropWhile p = c :: cs) : p c = false := by
  induction l with
  | nil => simp at hh
  | cons a as ih =>
    rw [List.dropWhile_cons] at hh
    split at hh
    · exact ih hh
    · rename_i hpa; rw [List.cons.injEq] at hh; obtain ⟨rfl, _⟩ := hh; simpa using hpa

/-- `tokenizeAux` from an empty accumulator skips leading separators. -/
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


/-! ## Flat tokenizer facts for `parse_complete` (a token followed by a separator
forms one token; separator runs are skipped). -/

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

/-- Interleave the *tail* of a token list: each token's leading run is `mkNESep`-
promoted to nonempty (matching the render's `gap`), while the state still advances
by the actual `readSeps` run. -/
def freBodyTail {G : Grammar} : List (Token G.isSep) → List Char → List Char × List Char
  | [],      rem => ([], rem)
  | t :: ts, rem =>
      let run := readSeps (G := G) rem
      let res := freBodyTail ts ((rem.drop run.length).drop t.val.toList.length)
      ((mkNESep run).toList.map (·.val) ++ t.val.toList ++ res.1, res.2)

/-- Interleave a token list over remaining chars: the first token's leading run is
plain `readSeps` (the possibly-empty `lead`); the rest go through `freBodyTail`
(nonempty `mkNESep` gaps). Returns (consumed chars, leftover). -/
def freBody {G : Grammar} : List (Token G.isSep) → List Char → List Char × List Char
  | [],      rem => ([], rem)
  | t :: ts, rem =>
      let run := readSeps (G := G) rem
      let res := freBodyTail ts ((rem.drop run.length).drop t.val.toList.length)
      (run.map (·.val) ++ t.val.toList ++ res.1, res.2)

/-- The full flat reassembly: consumed chars plus the trailing separator run. -/
def freBodyReassemble {G : Grammar} (toks : List (Token G.isSep)) (x : List Char) : List Char :=
  (freBody toks x).1 ++ (readSeps (G := G) (freBody toks x).2).map (·.val)

/-- `freBodyTail` collapses to `freBody` when the first read is nonempty (or there
are no tokens): the `mkNESep` promotion is then the identity. -/
theorem freBodyTail_eq_freBody {G : Grammar} (toks : List (Token G.isSep)) (rem : List Char)
    (h : toks = [] ∨ readSeps (G := G) rem ≠ []) :
    freBodyTail toks rem = freBody toks rem := by
  cases toks with
  | nil => rfl
  | cons t ts =>
    have hne : readSeps (G := G) rem ≠ [] := h.resolve_left (by simp)
    simp only [freBodyTail, freBody, mkNESep_toList_of_ne hne]

/-- **Tokenizer-inverse**: re-interleaving `input`'s tokens (`tokenize G input`) with
the separator runs read back off `input` reproduces `input` exactly. -/
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

/-! ## The cursor witness policy

`State := List Char` (remaining input). `lead`/`gap` emit `readSeps rem` and advance
past it; `step` drops the rendered token; `enter`/`exit` are identities (position is
carried by `step`, not by structure); `trail` is whatever separators remain. -/

def cursorPolicy {G : Grammar} (input : List Char) : Policy G where
  State   := List Char
  initial := input
  lead    := fun rem => (readSeps (G := G) rem, rem.drop (readSeps (G := G) rem).length)
  gap     := fun rem _ _ _ => (mkNESep (readSeps (G := G) rem), rem.drop (readSeps (G := G) rem).length)
  step    := fun rem t => rem.drop t.val.toList.length
  enter   := fun rem => rem
  exit    := fun rem => rem
  trail   := fun rem => readSeps (G := G) rem

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

/-- Appending onto a **nonempty** `toks1`: the first token stays plain (`freBody`),
the appended part is all-`freBodyTail`. -/
theorem freBody_append {G : Grammar} (toks1 toks2 : List (Token G.isSep)) (rem : List Char)
    (h : toks1 ≠ []) :
    freBody (toks1 ++ toks2) rem =
      ((freBody toks1 rem).1 ++ (freBodyTail toks2 (freBody toks1 rem).2).1,
       (freBodyTail toks2 (freBody toks1 rem).2).2) := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [List.cons_append, freBody, freBodyTail_append, List.append_assoc]

theorem toParts_ne_nil {G : Grammar} (n : Notation G.isSep G.Ent) :
    Notation.toParts (G := G) n ≠ [] := by cases n <;> simp [Notation.toParts]
theorem body_ne_nil {G : Grammar} (e : G.Ent) (o : (G.entry e).Op) :
    Operator.body e o ≠ [] := by unfold Operator.body; split <;> simp [toParts_ne_nil]

theorem freBody_lead {G : Grammar} (t : Token G.isSep) (ts : List (Token G.isSep)) (state : List Char)
    (hs0 : readSeps (G := G) (state.drop (readSeps (G := G) state).length) = []) :
    freBody (t :: ts) state =
      ((readSeps (G := G) state).map (·.val) ++
        (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).1,
       (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).2) := by
  simp only [freBody, hs0, List.length_nil, List.drop_zero, List.map_nil, List.nil_append,
    List.append_assoc]

/-- The `freBodyTail` analogue: the leading run is `mkNESep`-promoted, and the rest
is a plain `freBody` at the advanced state (its own first read is empty). -/
theorem freBodyTail_lead {G : Grammar} (t : Token G.isSep) (ts : List (Token G.isSep))
    (state : List Char)
    (hs0 : readSeps (G := G) (state.drop (readSeps (G := G) state).length) = []) :
    freBodyTail (t :: ts) state =
      ((mkNESep (readSeps (G := G) state)).toList.map (·.val) ++
        (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).1,
       (freBody (t :: ts) (state.drop (readSeps (G := G) state).length)).2) := by
  simp only [freBodyTail, freBody, hs0, List.length_nil, List.drop_zero, List.map_nil,
    List.nil_append, List.append_assoc]

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

theorem flatten_ne_nil {G : Grammar} {e : G.Ent} {l : Level (G.entry e)} (ex : Expr G e l) :
    ex.flatten ≠ [] := by
  induction ex using Expr.flatten.induct
    (motive_2 := fun {ps} prts => ps ≠ [] → Parts.flatten prts ≠ [])
  case case1 => rename_i o a ps ih; simp only [Expr.flatten]; exact ih (body_ne_nil _ _)
  case case2 => simp [Expr.flatten]
  case case3 => rename_i h; exact absurd rfl h
  case case4 => simp [Parts.flatten]
  case case5 => rename_i ih2 _ _; simp only [Parts.flatten]; intro hc; exact ih2 (List.append_eq_nil_iff.mp hc).1

theorem renderSp_INV {G : Grammar} (input : List Char) :
    ∀ (state : List Char) (lead : List (Sep G)) {e' : G.Ent} {l' : Level (G.entry e')}
      (ex' : Expr G e' l'), readSeps (G := G) state = [] →
      spacedToChars (Expr.renderSp (cursorPolicy input) state lead ex').1
        = lead.map (·.val) ++ (freBody ex'.flatten state).1
      ∧ (Expr.renderSp (cursorPolicy input) state lead ex').2 = (freBody ex'.flatten state).2 := by
  apply Expr.renderSp.induct (policy := cursorPolicy input)
    (motive_2 := fun state lead e' o {ps} prts => readSeps (G := G) state = [] → ps ≠ [] →
      spacedToChars (Parts.renderSp (cursorPolicy input) state lead e' o prts).1
        = lead.map (·.val) ++ (freBody prts.flatten state).1
      ∧ (Parts.renderSp (cursorPolicy input) state lead e' o prts).2 = (freBody prts.flatten state).2)
    (motive_3 := fun state e' o i {ps} prts =>
      spacedToChars (Parts.renderSpTail (cursorPolicy input) state e' o i prts).1
        = (freBodyTail prts.flatten state).1
      ∧ (Parts.renderSpTail (cursorPolicy input) state e' o i prts).2 = (freBodyTail prts.flatten state).2)
  case _ => -- var
    intro e' a state lead t hvar hrs
    refine ⟨?_, ?_⟩ <;>
      simp [Expr.renderSp, spacedToChars, Expr.flatten, freBody, freBodyTail, cursorPolicy, hrs]
  case _ => -- op
    intro e' a state lead o cond parts ih hrs
    simpa [Expr.renderSp, Expr.flatten] using ih hrs (body_ne_nil e' o)
  case _ => -- pnil
    intro state lead e' o hrs hne; exact absurd rfl hne
  case _ => -- pname
    intro state lead e' o ps tk rest rp s' heq m3 hrs _hne
    obtain ⟨m3a, m3b⟩ := m3
    simp only [heq, spacedToChars] at m3a m3b
    simp only [cursorPolicy] at m3a m3b
    refine ⟨?_, ?_⟩
    · simp only [Parts.renderSp, heq, spacedToChars, Parts.flatten, freBody, hrs,
        List.length_nil, List.drop_zero, List.map_nil, List.nil_append, List.flatMap_cons,
        List.append_assoc]
      rw [m3a]
    · simp only [Parts.renderSp, heq, Parts.flatten, freBody, hrs, List.length_nil, List.drop_zero]
      exact m3b
  case _ => -- phole
    intro state lead e' o e1 l1 ps ex rest rp s' heq1 rp2 s'2 heq2 m1 m3 hrs _hne
    obtain ⟨m1a, m1b⟩ := m1 hrs
    obtain ⟨m3a, m3b⟩ := m3
    simp only [heq1, spacedToChars] at m1a m1b
    simp only [cursorPolicy] at m1a m1b
    simp only [heq2, spacedToChars] at m3a m3b
    simp only [cursorPolicy] at m3a m3b
    have hfa := freBody_append ex.flatten rest.flatten state (flatten_ne_nil ex)
    refine ⟨?_, ?_⟩
    · simp only [Parts.renderSp, heq1, heq2, Parts.flatten, spacedToChars, List.flatMap_append, hfa]
      rw [m1a, m3a, m1b, List.append_assoc]
    · simp only [Parts.renderSp, heq1, heq2, Parts.flatten, hfa]
      rw [m3b, m1b]
  case _ => -- tnil
    intro state e' o i
    refine ⟨?_, ?_⟩ <;> simp [Parts.renderSpTail, spacedToChars, Parts.flatten, freBodyTail]
  case _ => -- tname
    intro state e' o i ps tk rest g s0 hgap rp s' heq m3
    obtain ⟨m3a, m3b⟩ := m3
    simp only [heq, spacedToChars] at m3a m3b
    simp only [cursorPolicy] at m3a m3b
    have hgap2 := hgap
    simp only [cursorPolicy, Prod.mk.injEq] at hgap2
    obtain ⟨hg, hs0⟩ := hgap2
    rw [← hs0] at m3a m3b
    refine ⟨?_, ?_⟩
    · simp only [Parts.renderSpTail, hgap, heq, spacedToChars, Parts.flatten, freBodyTail,
        List.flatMap_cons, List.append_assoc]
      rw [← hg, m3a]
    · simp only [Parts.renderSpTail, hgap, heq, Parts.flatten, freBodyTail]
      exact m3b
  case _ => -- thole
    intro state e' o i e1 l1 ps ex rest g s0 hgap rp s' heq1 rp2 s'2 heq2 m1 m3
    have hgap2 := hgap
    simp only [cursorPolicy, Prod.mk.injEq] at hgap2
    obtain ⟨hg, hs0⟩ := hgap2
    have hs0nil : readSeps (G := G) s0 = [] := by rw [← hs0, readSeps_drop]; exact readSeps_dropWhile state
    obtain ⟨m1a, m1b⟩ := m1 hs0nil
    obtain ⟨m3a, m3b⟩ := m3
    simp only [heq1, spacedToChars] at m1a m1b
    simp only [cursorPolicy] at m1a m1b
    simp only [heq2, spacedToChars] at m3a m3b
    simp only [cursorPolicy] at m3a m3b
    obtain ⟨t, ts, hts⟩ := List.exists_cons_of_ne_nil (flatten_ne_nil ex)
    have hfl := freBodyTail_lead (G := G) t ts state (by rw [readSeps_drop]; exact readSeps_dropWhile state)
    rw [← hts, hs0] at hfl
    rw [← hg] at m1a
    rw [m1b] at m3a m3b
    refine ⟨?_, ?_⟩
    · simp only [Parts.renderSpTail, hgap, heq1, heq2, Parts.flatten, spacedToChars,
        List.flatMap_append, freBodyTail_append, hfl]
      rw [m1a, m3a]
    · simp only [Parts.renderSpTail, hgap, heq1, heq2, Parts.flatten, freBodyTail_append, hfl]
      exact m3b

/-- **Claim 1 (structural)**: under the cursor policy the tree render equals the flat
reassembly of `ex`'s tokens over `input` — the render walks `ex` in lockstep with
`freBody`. No tokenizer reasoning here. -/
theorem render_eq_freBody {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (input : List Char) :
    renderExpr ex (cursorPolicy input) = freBodyReassemble ex.flatten input := by
  have hs0 : readSeps (G := G) (input.drop (readSeps (G := G) input).length) = [] := by
    rw [readSeps_drop]; exact readSeps_dropWhile input
  obtain ⟨h1, h2⟩ := renderSp_INV input (input.drop (readSeps (G := G) input).length)
    (readSeps (G := G) input) ex hs0
  show spacedToChars (Expr.renderSp (cursorPolicy input)
        (input.drop (readSeps (G := G) input).length) (readSeps (G := G) input) ex).1
      ++ (readSeps (G := G) (Expr.renderSp (cursorPolicy input)
        (input.drop (readSeps (G := G) input).length) (readSeps (G := G) input) ex).2).map (·.val)
      = freBodyReassemble ex.flatten input
  rw [h1, h2, freBodyReassemble_lead ex.flatten input]
  simp only [freBodyReassemble, List.append_assoc]

theorem cursor_render {G : Grammar} (input : List Char) {e : G.Ent}
    (ex : Expr G e .loosest) (h : ex ∈ parse e (tokenize G input)) :
    renderExpr ex (cursorPolicy input) = input := by
  rw [render_eq_freBody ex input, parse_sound h]
  exact freBody_tokenize G input.length input (Nat.le_refl _)

/-! ## `parse_complete`: `tokenize (renderExpr ex p) = ex.flatten` (from nonempty
`NESep` gaps and nonempty tokens), then membership in the prefix parser. -/

theorem spacedToChars_append {G : Grammar} (a b : List (List (Sep G) × Token G.isSep)) :
    spacedToChars (a ++ b) = spacedToChars a ++ spacedToChars b := by
  simp [spacedToChars, List.flatMap_append]

theorem spacedToChars_cons {G : Grammar} (q : List (Sep G) × Token G.isSep)
    (qs : List (List (Sep G) × Token G.isSep)) :
    spacedToChars (q :: qs) = (q.1.map (·.val) ++ q.2.val.toList) ++ spacedToChars qs := by
  simp [spacedToChars, List.flatMap_cons]

theorem renderSp_head {G : Grammar} (p : Policy G) :
    ∀ (state : p.State) (lead : List (Sep G)) {e' : G.Ent} {l' : Level (G.entry e')}
      (ex' : Expr G e' l'),
      ∃ rest, spacedToChars (Expr.renderSp p state lead ex').1 = lead.map (·.val) ++ rest := by
  apply Expr.renderSp.induct (policy := p)
    (motive_2 := fun state lead e' o {ps} prts => ps ≠ [] →
      ∃ rest, spacedToChars (Parts.renderSp p state lead e' o prts).1 = lead.map (·.val) ++ rest)
    (motive_3 := fun _ _ _ _ {_} _ => True)
  case _ => -- var
    intro e' a state lead t hvar; exact ⟨t.val.toList, by simp [Expr.renderSp, spacedToChars]⟩
  case _ => -- op
    intro e' a state lead o cond parts ih
    obtain ⟨rest, hrest⟩ := ih (body_ne_nil e' o)
    exact ⟨rest, by simpa [Expr.renderSp] using hrest⟩
  case _ => intro state lead e' o hne; exact absurd rfl hne   -- pnil
  case _ => -- pname
    intro state lead e' o ps tk rest rp s' heq m3 _hne
    exact ⟨tk.val.toList ++ spacedToChars rp, by simp [Parts.renderSp, heq, spacedToChars, List.append_assoc]⟩
  case _ => -- phole
    intro state lead e' o e1 l1 ps ex rest rp s' heq1 rp2 s'2 heq2 m1 m3 _hne
    obtain ⟨r, hr⟩ := m1
    simp only [heq1] at hr
    refine ⟨r ++ spacedToChars rp2, ?_⟩
    simp only [Parts.renderSp, heq1, heq2, spacedToChars_append, hr, List.append_assoc]
  case _ => intro state e' o i; trivial   -- tnil
  case _ => intro state e' o i ps tk rest g s0 hgap rp s' heq m3; trivial  -- tname
  case _ => intro state e' o i e1 l1 ps ex rest g s0 hgap rp s' heq1 rp2 s'2 heq2 m1 m3; trivial  -- thole

theorem rSpTail_takeWhile_nil {G : Grammar} (p : Policy G) (state : p.State) (e : G.Ent)
    (o : (G.entry e).Op) (i : Nat) {ps : List (Part G)} (rest : Parts G ps) :
    (spacedToChars (Parts.renderSpTail p state e o i rest).1).takeWhile (fun c => !G.isSep c) = [] := by
  cases rest with
  | nil => rfl
  | namePart tk rest' =>
    simp only [Parts.renderSpTail, spacedToChars, NESep.toList, List.flatMap_cons, List.map_cons,
      List.cons_append, List.takeWhile_cons]
    simp [(p.gap state e o i).1.head.2]
  | hole ex rest' =>
    simp only [Parts.renderSpTail]
    obtain ⟨r, hr⟩ := renderSp_head p (p.enter (p.gap state e o i).2) (p.gap state e o i).1.toList ex
    rw [spacedToChars_append, hr, NESep.toList]
    simp only [List.map_cons, List.cons_append, List.takeWhile_cons]
    simp [(p.gap state e o i).1.head.2]

theorem tokenize_render_INV {G : Grammar} (p : Policy G) :
    ∀ (state : p.State) (lead : List (Sep G)) {e' : G.Ent} {l' : Level (G.entry e')}
      (ex' : Expr G e' l') (suffix : List Char),
      suffix.takeWhile (fun c => !G.isSep c) = [] →
      tokenize G (spacedToChars (Expr.renderSp p state lead ex').1 ++ suffix)
        = ex'.flatten ++ tokenize G suffix := by
  apply Expr.renderSp.induct (policy := p)
    (motive_2 := fun state lead e' o {ps} prts => ∀ (suffix : List Char),
      suffix.takeWhile (fun c => !G.isSep c) = [] → ps ≠ [] →
      tokenize G (spacedToChars (Parts.renderSp p state lead e' o prts).1 ++ suffix)
        = prts.flatten ++ tokenize G suffix)
    (motive_3 := fun state e' o i {ps} prts => ∀ (suffix : List Char),
      suffix.takeWhile (fun c => !G.isSep c) = [] →
      tokenize G (spacedToChars (Parts.renderSpTail p state e' o i prts).1 ++ suffix)
        = prts.flatten ++ tokenize G suffix)
  case _ => -- var
    intro e' a state lead t hvar suffix hsuf
    simp only [Expr.renderSp, spacedToChars, Expr.flatten, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [List.append_assoc, tokenize_sep_prefix, tokenize_token t suffix hsuf, List.singleton_append]
  case _ => -- op
    intro e' a state lead o cond parts ih suffix hsuf
    simpa [Expr.renderSp, Expr.flatten] using ih suffix hsuf (body_ne_nil e' o)
  case _ => intro state lead e' o suffix hsuf hne; exact absurd rfl hne  -- pnil
  case _ => -- pname
    intro state lead e' o ps tk rest rp s' heq m3 suffix hsuf _hne
    have h1 : (spacedToChars rp).takeWhile (fun c => !G.isSep c) = [] := by
      have := rSpTail_takeWhile_nil p (p.step state tk) e' o 0 rest; rw [heq] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) _ suffix h1 hsuf
    simp only [heq] at m3
    simp only [Parts.renderSp, heq, spacedToChars_cons, Parts.flatten, List.append_assoc]
    rw [tokenize_sep_prefix, tokenize_token tk _ hcond, m3 suffix hsuf, List.cons_append]
  case _ => -- phole
    intro state lead e' o e1 l1 ps ex rest rp s' heq1 rp2 s'2 heq2 m1 m3 suffix hsuf _hne
    have h2 : (spacedToChars rp2).takeWhile (fun c => !G.isSep c) = [] := by
      have := rSpTail_takeWhile_nil p (p.exit s') e' o 0 rest; rw [heq2] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) _ suffix h2 hsuf
    simp only [heq1] at m1
    simp only [heq2] at m3
    simp only [Parts.renderSp, heq1, heq2, spacedToChars_append, Parts.flatten, List.append_assoc]
    rw [m1 (spacedToChars rp2 ++ suffix) hcond, m3 suffix hsuf]
  case _ => -- tnil
    intro state e' o i suffix hsuf
    simp [Parts.renderSpTail, spacedToChars, Parts.flatten]
  case _ => -- tname
    intro state e' o i ps tk rest g s0 hgap rp s' heq m3 suffix hsuf
    have h1 : (spacedToChars rp).takeWhile (fun c => !G.isSep c) = [] := by
      have := rSpTail_takeWhile_nil p (p.step s0 tk) e' o (i+1) rest; rw [heq] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) _ suffix h1 hsuf
    simp only [heq] at m3
    simp only [Parts.renderSpTail, hgap, heq, spacedToChars_cons, Parts.flatten, List.append_assoc]
    rw [tokenize_sep_prefix, tokenize_token tk _ hcond, m3 suffix hsuf, List.cons_append]
  case _ => -- thole
    intro state e' o i e1 l1 ps ex rest g s0 hgap rp s' heq1 rp2 s'2 heq2 m1 m3 suffix hsuf
    have h2 : (spacedToChars rp2).takeWhile (fun c => !G.isSep c) = [] := by
      have := rSpTail_takeWhile_nil p (p.exit s') e' o (i+1) rest; rw [heq2] at this; exact this
    have hcond := takeWhile_append_nil (fun c => !G.isSep c) _ suffix h2 hsuf
    simp only [heq1] at m1
    simp only [heq2] at m3
    simp only [Parts.renderSpTail, hgap, heq1, heq2, spacedToChars_append, Parts.flatten,
      List.append_assoc]
    rw [m1 (spacedToChars rp2 ++ suffix) hcond, m3 suffix hsuf]

theorem sepRun_takeWhile_nil {G : Grammar} (run : List (Sep G)) :
    (run.map (·.val)).takeWhile (fun c => !G.isSep c) = [] := by
  cases run with
  | nil => rfl
  | cons s run' => simp [List.map_cons, List.takeWhile_cons, s.2]

theorem tokenize_renderExpr {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (p : Policy G) :
    tokenize G (renderExpr ex p) = ex.flatten := by
  unfold renderExpr
  rw [tokenize_render_INV p _ _ ex _ (sepRun_takeWhile_nil _)]
  rw [show ((p.trail (Expr.renderSp p (p.lead p.initial).2 (p.lead p.initial).1 ex).2).map (·.val))
        = ((p.trail (Expr.renderSp p (p.lead p.initial).2 (p.lead p.initial).1 ex).2).map (·.val)) ++ []
      from (List.append_nil _).symm, tokenize_sep_prefix, tokenize_nil G [] rfl, List.append_nil]

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

theorem char_parse_complete {G : Grammar} {e : G.Ent} (ex : Expr G e .loosest) (p : Policy G)
    (rest : List Char) :
    ∃ s : RightSublist (renderExpr ex p ++ rest),
      s.list = rest ∧ (ex, s) ∈ parseChars e (renderExpr ex p ++ rest) := by
  have htok : tokenize G (renderExpr ex p) = ex.flatten := tokenize_renderExpr ex p
  have hne : renderExpr ex p ≠ [] := fun h =>
    flatten_ne_nil ex (by rw [← htok, h]; exact tokenize_nil G [] rfl)
  have hpos : 0 < (renderExpr ex p).length := List.length_pos_iff.mpr hne
  have hlt : (renderExpr ex p).length - 1 < (renderExpr ex p ++ rest).length := by
    rw [List.length_append]; omega
  have hex : ex ∈ parse e
      (tokenize G ((renderExpr ex p ++ rest).take ((renderExpr ex p).length - 1 + 1))) := by
    rw [Nat.sub_add_cancel hpos, List.take_left, htok]; exact parse_complete ex
  refine ⟨_, ?_, mem_parseChars hlt hex⟩
  show (renderExpr ex p ++ rest).drop ((renderExpr ex p).length - 1 + 1) = rest
  rw [Nat.sub_add_cancel hpos, List.drop_left]

/-- The mixfix biparser at start entry `e`. `render_complete` is `cursor_render`;
`parse_complete` is `char_parse_complete` (prefix `parseChars` + `tokenize (render) =
flatten`). -/
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
      exact ⟨cursorPolicy ((c :: cs).take (n + 1)),
        cursor_render ((c :: cs).take (n + 1)) ex' hex'⟩
  parse_complete := char_parse_complete

/-- The **token-level** mixfix biparser (verified): `render = flatten`, trivial
`Policy`, both laws from `parseExpr_sound`/`parseExpr_complete`. -/
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

end LambdaLab.Parser2.Mixfix
