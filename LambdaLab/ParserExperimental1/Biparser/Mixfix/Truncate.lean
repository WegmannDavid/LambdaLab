import LambdaLab.ParserExperimental1.Biparser.Mixfix.Complete

/-!
# A truncating biparser for the mixfix grammar

The precedence-indexed `Tree G p` carries **explicit `paren` nodes**, so `(a)`, `((a))`,
and `a` are distinct trees with distinct renders — the full `mixfixBip` keeps both laws by
distinguishing them. A **`TruncatingBiparser`** instead maps onto a *lossy* value type
`Term G` (a paren-free AST): `parse` erases parens, `render` emits a single canonical
(here **fully-parenthesized**) form, and only `parse_complete` survives — `render_complete`
genuinely fails, because `"a + b"`, `"(a) + b"`, `"( a + b )"` all parse to the same
`Term` but `render` reproduces none of them verbatim.

The lever is a generic `truncateLift`: any weak `Biparser α P β` plus a lossy
`interp : β → γ`, a section `revInterp : γ → β`, and `interp ∘ revInterp = id` yields a
`TruncatingBiparser α γ`. Here `revInterp` **fully parenthesizes** — since `Tree.paren` is
level-polymorphic it fits every operand slot, sidestepping precedence-aware minimal
parenthesization — which makes the section law immediate.
-/

namespace LambdaLab.ParserExperimental1.Mixfix

open LambdaLab.ParserExperimental1

/-- Lift a weak `Biparser` to a `TruncatingBiparser` along a lossy `interp` with a section
`revInterp` (`interp ∘ revInterp = id`), baking in the policy `pol`. -/
def truncateLift {α P β γ : Type} (bp : Biparser α P β) (interp : β → γ) (revInterp : γ → β)
    (pol : P) (hsec : ∀ t, interp (revInterp t) = t) : TruncatingBiparser α γ where
  render t := bp.render (revInterp t) pol
  parse input := (bp.parse input).map (fun r => (interp r.1, r.2))
  parse_complete := by
    intro b rest
    obtain ⟨s, hs, hmem⟩ := bp.parse_complete (revInterp b) pol rest
    exact ⟨s, hs, List.mem_map.mpr ⟨(revInterp b, s), hmem, by rw [hsec]⟩⟩

/-! ### The lossy, paren-free term. -/

mutual
/-- A paren-free abstract syntax tree — `Tree G p` with the `paren` nodes and precedence
index erased (but the operator's `hk`/fixity proofs kept, so it renders back). -/
inductive Term (G : Grammar) where
  | var  : VarTok G → Term G
  | op   (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .infixr) :
            Term G → Term G → Term G
  | opl  (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .infixl) :
            Term G → Term G → TermChain G → Term G
  | opn  (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .infixNon) :
            Term G → Term G → Term G
  | pre  (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .prefix) : Term G → Term G
  | post (k : Nat) (hk : k < G.ops.length) (hfix : G.opFixity k hk = .postfix) : Term G → Term G
  | jux  (hj : G.juxt = true) : Term G → Term G → TermChain G → Term G
inductive TermChain (G : Grammar) where
  | nil  : TermChain G
  | cons : Term G → TermChain G → TermChain G
end

/-! ### `interp` — erase parens (`Tree → Term`). -/

mutual
def Interp {G : Grammar} : {p : Nat} → Tree G p → Term G
  | _, .var v                              => .var v
  | _, .paren t                            => Interp t
  | _, .op k hk hfix _ l r                 => .op k hk hfix (Interp l) (Interp r)
  | _, .opl k hk hfix _ head chd chr       => .opl k hk hfix (Interp head) (Interp chd) (interpChain chr)
  | _, .opn k hk hfix _ l r                => .opn k hk hfix (Interp l) (Interp r)
  | _, .pre k hk hfix _ e                  => .pre k hk hfix (Interp e)
  | _, .post k hk hfix _ e                 => .post k hk hfix (Interp e)
  | _, .jux hj _ head chd chr              => .jux hj (Interp head) (Interp chd) (interpChain chr)
def interpChain {G : Grammar} : {n : Nat} → TreeChain G n → TermChain G
  | _, .nil       => .nil
  | _, .cons t ts => .cons (Interp t) (interpChain ts)
end

/-! ### `revAt` — reconstruct a **minimally-parenthesized** `Tree G ℓ` (`Term → Tree`).

Build the operator node directly at the required level `ℓ` when it binds tightly enough
(`ℓ ≤ k`); otherwise the node is too loose for the slot, so wrap it in a single `paren`
(at level 0). Only *necessary* parentheses are emitted. Structural in the term. -/

mutual
def revAt {G : Grammar} (ℓ : Nat) : Term G → Tree G ℓ
  | .var v => .var v
  | .op k hk hfix l r =>
      if h : ℓ ≤ k then .op k hk hfix h (revAt (k + 1) l) (revAt k r)
      else .paren (.op k hk hfix (Nat.zero_le k) (revAt (k + 1) l) (revAt k r))
  | .opl k hk hfix head chd chr =>
      if h : ℓ ≤ k then
        .opl k hk hfix h (revAt (k + 1) head) (revAt (k + 1) chd) (revChainAt (k + 1) chr)
      else .paren (.opl k hk hfix (Nat.zero_le k)
        (revAt (k + 1) head) (revAt (k + 1) chd) (revChainAt (k + 1) chr))
  | .opn k hk hfix l r =>
      if h : ℓ ≤ k then .opn k hk hfix h (revAt (k + 1) l) (revAt (k + 1) r)
      else .paren (.opn k hk hfix (Nat.zero_le k) (revAt (k + 1) l) (revAt (k + 1) r))
  | .pre k hk hfix e =>
      if h : ℓ ≤ k then .pre k hk hfix h (revAt (k + 1) e)
      else .paren (.pre k hk hfix (Nat.zero_le k) (revAt (k + 1) e))
  | .post k hk hfix e =>
      if h : ℓ ≤ k then .post k hk hfix h (revAt (k + 1) e)
      else .paren (.post k hk hfix (Nat.zero_le k) (revAt (k + 1) e))
  | .jux hj head chd chr =>
      if h : ℓ ≤ G.ops.length then .jux hj h
        (revAt (G.ops.length + 1) head) (revAt (G.ops.length + 1) chd)
        (revChainAt (G.ops.length + 1) chr)
      else .paren (.jux hj (Nat.zero_le _)
        (revAt (G.ops.length + 1) head) (revAt (G.ops.length + 1) chd)
        (revChainAt (G.ops.length + 1) chr))
def revChainAt {G : Grammar} (m : Nat) : TermChain G → TreeChain G m
  | .nil       => .nil
  | .cons t ts => .cons (revAt m t) (revChainAt m ts)
end

/-! ### The section law: `interp (revAt ℓ t) = t` (for any required level `ℓ`). -/

mutual
theorem interp_revAt {G : Grammar} : (ℓ : Nat) → (t : Term G) → Interp (revAt ℓ t) = t
  | _, .var _              => rfl
  | ℓ, .op k hk hfix l r   => by
      simp only [revAt]; split <;> simp only [Interp, interp_revAt (k + 1) l, interp_revAt k r]
  | ℓ, .opl k hk hfix head chd chr => by
      simp only [revAt]; split <;> simp only [Interp, interp_revAt (k + 1) head,
        interp_revAt (k + 1) chd, interp_revChainAt (k + 1) chr]
  | ℓ, .opn k hk hfix l r  => by
      simp only [revAt]; split <;>
        simp only [Interp, interp_revAt (k + 1) l, interp_revAt (k + 1) r]
  | ℓ, .pre k hk hfix e    => by
      simp only [revAt]; split <;> simp only [Interp, interp_revAt (k + 1) e]
  | ℓ, .post k hk hfix e   => by
      simp only [revAt]; split <;> simp only [Interp, interp_revAt (k + 1) e]
  | ℓ, .jux hj head chd chr => by
      simp only [revAt]; split <;> simp only [Interp, interp_revAt (G.ops.length + 1) head,
        interp_revAt (G.ops.length + 1) chd, interp_revChainAt (G.ops.length + 1) chr]
theorem interp_revChainAt {G : Grammar} : (m : Nat) → (ts : TermChain G) →
    interpChain (revChainAt m ts) = ts
  | _, .nil       => rfl
  | m, .cons t ts => by
      simp only [revChainAt, interpChain, interp_revAt m t, interp_revChainAt m ts]
end

/-- The truncating mixfix biparser: parse chars into a paren-free `Term G` (parens erased),
render a `Term` back to its canonical **minimally-parenthesized** form. Only
`parse_complete` holds — `render_complete` fails, since many surface strings map to one
`Term`. -/
def mixfixTrunc {G : Grammar} : TruncatingBiparser Char (Term G) :=
  truncateLift mixfixBip Interp (revAt 0) (fun _ => 0) (interp_revAt 0)

#eval String.ofList (mixfixTrunc.render (Interp sampleTree))     -- "a + b * c" (no redundant parens)
#eval String.ofList (mixfixTrunc.render (Interp sampleLTree))    -- "a +. b +. c"

end LambdaLab.ParserExperimental1.Mixfix
