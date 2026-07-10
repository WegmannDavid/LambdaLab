import LambdaLab.Biparser.Mixfix.Tree

/-!
# The single canonical print: `Expr` → `List Char`

No `Policy`, no `Layout`, no state threading. The rendering of a tree is fixed:
each operator body is its parts in order, separated by exactly **one** `sepWitness`
character (the minimal legal gap), holes rendered recursively; a variable leaf is
its token. No leading or trailing whitespace.

This is precisely the old `defaultPolicy` — but baked in as *the* printer, since
we no longer care about alternative rendering policies. Parenthesization is not
handled here: this grammar has no paren constructor, so parens are just a
user-defined `closed` operator and fall out of the structural walk.
-/

namespace LambdaLab.Biparser.Mixfix

/-- The canonical inter-part separator: a single `sepWitness` character. -/
def sepChar (G : Grammar) : List Char := [G.sepWitness.val]

mutual
  /-- The single canonical printing of a tree. -/
  def Expr.print {G : Grammar} {e : G.Ent} {l : Level (G.entry e)} :
      Expr G e l → List Char
    | .op _ _ parts => Parts.print parts
    | .var t _      => t.val.toList

  /-- Print a body from its first part — no leading separator. -/
  def Parts.print {G : Grammar} {shape : List (Part G)} : Parts G shape → List Char
    | .nil              => []
    | .namePart tk rest => tk.val.toList ++ Parts.printTail rest
    | .hole ex rest     => Expr.print ex ++ Parts.printTail rest

  /-- Print the remaining parts — one `sepWitness` char before each. -/
  def Parts.printTail {G : Grammar} {shape : List (Part G)} : Parts G shape → List Char
    | .nil              => []
    | .namePart tk rest => sepChar G ++ tk.val.toList ++ Parts.printTail rest
    | .hole ex rest     => sepChar G ++ Expr.print ex ++ Parts.printTail rest
end

end LambdaLab.Biparser.Mixfix
