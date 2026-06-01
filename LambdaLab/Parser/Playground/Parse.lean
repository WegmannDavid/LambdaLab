import LambdaLab.Parser.Basic
import LambdaLab.Parser.Playground.Tree

/-!
# Parsing closed operators

Because every operator is *closed* (it starts with a literal name-part),
the first token of a token stream determines the operator via `G.lookup`.
Once the operator is fixed, its `OpDesc` dictates the rest: we alternately
consume name-part tokens and recurse into holes.

The recursion threads the *leftover* tokens through each sub-parse, and that
leftover is not a structural subterm of the input — so plain structural
recursion is rejected. The fix is to make "tokens were consumed" visible *in
the type*: each parser returns a `RightSublist tkns`, a proper suffix of its
input. A proper suffix is strictly shorter (`RightSublist.length_lt`), which
gives a well-founded measure (`tkns.length`) for `termination_by`.
-/

namespace LambdaLab.Parser.Playground

mutual
  /-- Parse one tree off the front of `tkns`, returning it with the unconsumed
  remainder as a proper suffix. The first token selects the operator;
  `parseChildren` handles the operator's full shape (re-consuming that token). -/
  def parseTree {G : Grammar} (tkns : List Token) :
      Option (Tree G × RightSublist tkns) :=
    match tkns with
    | [] => none
    | tk :: rest =>
        match G.lookup tk with
        | some o => (parseChildren (G.OpDescs o) (tk :: rest)).map fun (cs, r) => (.op o cs, r)
        | none => none
  termination_by 2 * tkns.length + 1
  decreasing_by simp_wf; try omega

  /-- Parse the name-parts and holes prescribed by `d` off the front of `tkns`.
  Each `.part t` consumes the literal `t`, then a child tree; `.last t` consumes
  the trailing `t` and stops. The returned remainder is a proper suffix because
  at least the leading name-part is always consumed. -/
  def parseChildren {G : Grammar} (d : OpDesc n) (tkns : List Token) :
      Option (Children G n × RightSublist tkns) :=
    match d, tkns with
    | .last t, tk :: rest =>
        if t = tk then some (.last, .cons tk rest) else none
    | .part t d', tk :: rest =>
        if t = tk then
          match parseTree rest with
          | some (child, rest') =>
              (parseChildren d' rest'.list).map fun (children, r) =>
                (.part child children, (RightSublist.cons tk rest).trans (rest'.trans r))
          | none => none
        else none
    | _, [] => none
  termination_by 2 * tkns.length
  decreasing_by
    all_goals simp_wf
    all_goals first
      | ((try simp only [List.length_cons]); omega)
      | (have h := rest'.length_lt; (try simp only [List.length_cons]); omega)
end

def parser (G : Grammar) : Parser (Tree G) := parseTree

end LambdaLab.Parser.Playground
