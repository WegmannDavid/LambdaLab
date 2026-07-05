import LambdaLab.Parser1.Mixfix.Biparse

/-!
# A tiny grammar exercising the char-level biparser

One entry (`Unit`) with three operators — parentheses, application (`juxt`), and a
left-assoc `+` — over an alphabet where the only separator is the space. Tokens are
now separator-free by construction (`Token arithSep`), so each name-part literal
carries a `by decide` proof (via the `tk` helper). A trivial single-space `Policy`
lets us `#eval` a full char round-trip.
-/

namespace LambdaLab.Parser1.Mixfix

open LambdaLab.Parser1

/-- Space is the only separator. -/
def arithSep : Char → Bool := fun c => c == ' '

/-- A separator-free token literal — the sep-free proof is discharged by `decide`. -/
def tk (s : String) (h : (∀ c ∈ s.toList, arithSep c = false) ∧ s.toList ≠ [] := by decide) :
    Token arithSep :=
  ⟨s, h⟩

/-- Operators of the single entry: `( _ )`, application, and `_ + _`. -/
inductive PSym | paren | app | plus
  deriving DecidableEq, Repr

def preserved : List (Token arithSep) := [tk "(", tk ")", tk "+"]

def psymTighter : PSym → List PSym
  | .plus  => [.app]
  | .app   => [.paren]
  | .paren => []

def psymRank : PSym → Nat
  | .paren => 0 | .app => 1 | .plus => 2

theorem psymTighter_wf : WellFounded (fun b a => b ∈ psymTighter a) :=
  Subrelation.wf
    (r := fun x y => psymRank x < psymRank y)
    (fun {x y} (h : x ∈ psymTighter y) => by
      cases x <;> cases y <;> simp_all [psymTighter, psymRank])
    (measure psymRank).wf

def psymOp : PSym → Operator arithSep Unit
  | .paren => .closed (.cons (tk "(") () (.last (tk ")")))
  | .app   => .juxt
  | .plus  => .infxl (.last (tk "+"))

def pEntry : Entry arithSep Unit where
  Op := PSym
  operator := psymOp
  loosest := [.plus]
  tighter := psymTighter
  tighter_wf := psymTighter_wf
  isVar := fun t => decide (t ∉ preserved)
  juxtUnique := fun o₁ o₂ h₁ h₂ => by cases o₁ <;> cases o₂ <;> simp_all [psymOp]

/-- The grammar: one entry, space is the only separator. -/
def arith : Grammar where
  Ent := Unit
  isSep := arithSep
  sepWitness := ⟨' ', by decide⟩
  entry := fun _ => pEntry

/-- A single space, as a nonempty separator run of `arith`. -/
def spaceSep : NESep arith := ⟨⟨' ', by decide⟩, []⟩

/-- The trivial policy: stateless, no edges anywhere, a single space at every
internal gap. -/
def spacePolicy : Policy arith where
  State := Unit
  initial := ()
  traverse    := fun e o s => Layout.const spaceSep s (Operator.body e o)
  traverseVar := fun _ _ _ => ([], [])

/-- Parse a source string at the single entry, render every parse back under
`spacePolicy`, and show the resulting strings — a full char round-trip. -/
def roundTrip (s : String) : List String :=
  (parseChars (G := arith) () s.toList).map (fun r => String.ofList (renderExpr r.1 spacePolicy))

#eval roundTrip "x"              -- ["x"]
#eval roundTrip "f x"            -- application
#eval roundTrip "f x y"          -- left-assoc application
#eval roundTrip "a + b"          -- infix +
#eval roundTrip "a + b + c"      -- left-assoc +
#eval roundTrip "( f x )"        -- parentheses preserved
#eval roundTrip "a + f x"        -- + looser than application
#eval roundTrip "f x  +  y"      -- extra spaces collapse to canonical

end LambdaLab.Parser1.Mixfix
