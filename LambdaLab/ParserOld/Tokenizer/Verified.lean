import LambdaLab.ParserOld.Tokenizer.Renders

/-!
# Tokenizer correctness

The forward map `tokenize` is characterized by the reverse relation `Renders`,
in the same shape as the parser's `mem_parse_iff : e ∈ parse tkns ↔ e.flatten = tkns`,
so the biconditionals compose along the pipeline:

    tok_eq_iff      : tok cs = ws ↔ RendersChars ws cs
    tokenize_eq_iff : tokenize s = ts ↔ Renders ts s

Substituting `ts := e.flatten` and chaining with `mem_parse_iff` gives the front
half of the pipeline as a single relation, `e ∈ parse (tokenize s) ↔ Renders e.flatten s`.
-/

namespace LambdaLab.ParserOld
namespace Tokenizer

/-- Forward: the actual token split is a valid rendering of the input. -/
theorem tok_renders : (cs : List Char) → RendersChars (tok cs) cs
  | cs => by
    cases h : skipWS cs with
    | nil =>
        rw [tok_nil h]
        exact ⟨cs, [], all_of_dropWhile_eq_nil h, (List.append_nil cs).symm,
               RendersCore.nil (by intro c hc; simp at hc)⟩
    | cons c rest =>
        rw [tok_cons h]
        have hc_tok : isTokChar c = true := by
          have : c.isWhitespace = false := not_p_head_dropWhile _ h
          simp [isTokChar, this]
        obtain ⟨g2, body2, hg2, hcs2, hrc2⟩ := tok_renders (afterWord (c :: rest))
        have hwd : word (c :: rest) ++ afterWord (c :: rest) = c :: rest := by
          unfold word afterWord; exact List.takeWhile_append_dropWhile
        have hword : IsWord (word (c :: rest)) := by
          refine ⟨?_, ?_⟩
          · show (c :: rest).takeWhile isTokChar ≠ []
            rw [List.takeWhile_cons]; simp [hc_tok]
          · intro x hx
            have hx' : x ∈ (c :: rest).takeWhile isTokChar := hx
            have := mem_takeWhile hx'; simp [isTokChar] at this; exact this
        have hsep : tok (afterWord (c :: rest)) ≠ [] → g2 ≠ [] := by
          intro hne hg2nil
          subst hg2nil
          rw [List.nil_append] at hcs2
          have hb2 : body2 ≠ [] := rendersCore_ne_nil hrc2 hne
          cases hbody : body2 with
          | nil => exact hb2 hbody
          | cons a r =>
              have haw : afterWord (c :: rest) = a :: r := by rw [hcs2, hbody]
              have h_ws : a.isWhitespace = true := afterWord_head_ws haw
              have h_nonws : a.isWhitespace = false :=
                rendersCore_head_ws_false (hbody ▸ hrc2) hne
              rw [h_ws] at h_nonws; simp at h_nonws
        have heq : c :: rest = word (c :: rest) ++ g2 ++ body2 := by
          rw [List.append_assoc, ← hcs2, hwd]
        refine ⟨cs.takeWhile (·.isWhitespace), c :: rest,
               (fun x hx => mem_takeWhile hx), ?_,
               RendersCore.cons hword hg2 hsep hrc2 heq⟩
        have hh : (c :: rest) = cs.dropWhile (·.isWhitespace) := h.symm
        rw [hh]; exact List.takeWhile_append_dropWhile.symm
  termination_by cs => cs.length
  decreasing_by exact length_afterWord_lt h

/-- Backward: every valid rendering tokenizes to its token list. (Lean's
`induction` keeps the inductive hypothesis `ih : tok cs = ws'`, used at the end.) -/
theorem rendersCore_tok {ws body} (h : RendersCore ws body) : tok body = ws := by
  induction h with
  | nil hg => exact tok_nil (dropWhile_eq_nil_of_all (fun c hc => hg c hc))
  | @cons w g cs ws' body hw hg hsep hrc hbody ih =>
      rw [hbody, List.append_assoc]
      obtain ⟨w0, w', rfl⟩ : ∃ w0 w', w = w0 :: w' := by
        cases w with
        | nil => exact absurd rfl hw.1
        | cons w0 w' => exact ⟨w0, w', rfl⟩
      have hw0 : w0.isWhitespace = false := hw.2 w0 (by simp)
      have hw_all : ∀ c ∈ w0 :: w', isTokChar c = true := fun c hc => by
        have := hw.2 c hc; simp [isTokChar, this]
      have hr_tok : ∀ a r, g ++ cs = a :: r → isTokChar a = false := by
        intro a r hgcs
        cases g with
        | cons x xs =>
            rw [List.cons_append] at hgcs
            have hx : x.isWhitespace = true := hg x (by simp)
            rw [(List.cons.inj hgcs).1] at hx; simp [isTokChar, hx]
        | nil =>
            rw [List.nil_append] at hgcs
            have hws' : ws' = [] := Classical.byContradiction (fun hne => hsep hne rfl)
            subst hws'
            cases hrc with
            | nil hcsws =>
                have haws : a.isWhitespace = true := hcsws a (by rw [hgcs]; simp)
                simp [isTokChar, haws]
      have hskip : skipWS ((w0 :: w') ++ (g ++ cs)) = w0 :: (w' ++ (g ++ cs)) := by
        simp [skipWS, List.cons_append, hw0]
      rw [tok_cons hskip]
      have hword : word (w0 :: (w' ++ (g ++ cs))) = w0 :: w' :=
        takeWhile_append_eq hw_all hr_tok
      have hafter : afterWord (w0 :: (w' ++ (g ++ cs))) = g ++ cs :=
        dropWhile_append_eq hw_all hr_tok
      rw [hword, hafter, tok_ws_prepend hg, ih]

/-! ### The composable characterizations -/

theorem tok_eq_iff {cs : List Char} {ws : List (List Char)} :
    tok cs = ws ↔ RendersChars ws cs := by
  constructor
  · intro h; rw [← h]; exact tok_renders cs
  · rintro ⟨g, body, hg, rfl, hrc⟩
    rw [tok_ws_prepend hg]; exact rendersCore_tok hrc

theorem tokenize_eq_iff {s : String} {ts : List Token} :
    tokenize s = ts ↔ Renders ts s := by
  rw [Renders, ← tok_eq_iff, tokenize]
  constructor
  · intro h
    rw [← h, List.map_map]
    have hid : (String.toList ∘ String.ofList) = id := funext fun _ => String.toList_ofList
    rw [hid, List.map_id]
  · intro h
    rw [h, List.map_map]
    have hid : (String.ofList ∘ String.toList) = id := funext fun _ => String.ofList_toList
    rw [hid, List.map_id]

end Tokenizer
end LambdaLab.ParserOld
