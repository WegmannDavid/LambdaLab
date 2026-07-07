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

/-! ### `revInterp` — reconstruct a fully-parenthesized `Tree G 0` (`Term → Tree`). -/

mutual
def RevInterp {G : Grammar} : Term G → Tree G 0
  | .var v                => .var v
  | .op k hk hfix l r     => .op k hk hfix (Nat.zero_le k) (.paren (RevInterp l)) (.paren (RevInterp r))
  | .opl k hk hfix head chd chr =>
      .opl k hk hfix (Nat.zero_le k) (.paren (RevInterp head)) (.paren (RevInterp chd)) (revChain chr)
  | .opn k hk hfix l r    => .opn k hk hfix (Nat.zero_le k) (.paren (RevInterp l)) (.paren (RevInterp r))
  | .pre k hk hfix e      => .pre k hk hfix (Nat.zero_le k) (.paren (RevInterp e))
  | .post k hk hfix e     => .post k hk hfix (Nat.zero_le k) (.paren (RevInterp e))
  | .jux hj head chd chr  =>
      .jux hj (Nat.zero_le _) (.paren (RevInterp head)) (.paren (RevInterp chd)) (revChain chr)
def revChain {G : Grammar} : {n : Nat} → TermChain G → TreeChain G n
  | _, .nil       => .nil
  | _, .cons t ts => .cons (.paren (RevInterp t)) (revChain ts)
end

/-! ### The section law: `interp ∘ revInterp = id`. -/

mutual
theorem interp_revInterp {G : Grammar} : (t : Term G) → Interp (RevInterp t) = t
  | .var _              => rfl
  | .op k hk hfix l r   => by
      simp only [RevInterp, Interp, interp_revInterp l, interp_revInterp r]
  | .opl k hk hfix head chd chr => by
      simp only [RevInterp, Interp, interp_revInterp head, interp_revInterp chd, interp_revChain chr]
  | .opn k hk hfix l r  => by
      simp only [RevInterp, Interp, interp_revInterp l, interp_revInterp r]
  | .pre k hk hfix e    => by simp only [RevInterp, Interp, interp_revInterp e]
  | .post k hk hfix e   => by simp only [RevInterp, Interp, interp_revInterp e]
  | .jux hj head chd chr => by
      simp only [RevInterp, Interp, interp_revInterp head, interp_revInterp chd, interp_revChain chr]
theorem interp_revChain {G : Grammar} {n : Nat} : (ts : TermChain G) →
    interpChain (revChain (n := n) ts) = ts
  | .nil       => rfl
  | .cons t ts => by
      simp only [revChain, interpChain, Interp, interp_revInterp t, interp_revChain ts]
end

/-- The truncating mixfix biparser: parse chars into a paren-free `Term G` (parens erased),
render a `Term` back to its canonical fully-parenthesized form. Only `parse_complete`
holds — `render_complete` fails, since many surface strings map to one `Term`. -/
def mixfixTrunc {G : Grammar} : TruncatingBiparser Char (Term G) :=
  truncateLift mixfixBip Interp RevInterp (fun _ => 0) interp_revInterp

#eval String.ofList (mixfixTrunc.render (Interp sampleTree))     -- fully parenthesized "a + b * c"
#eval String.ofList (mixfixTrunc.render (Interp sampleLTree))    -- fully parenthesized "a +. b +. c"

end LambdaLab.ParserExperimental1.Mixfix
