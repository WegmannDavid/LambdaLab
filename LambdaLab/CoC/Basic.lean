/-!
# The sorts of CoC — shared vocabulary above both presentations

`*` and `□` mention no variables, so they are the one piece of syntax the named and de Bruijn
variants literally share rather than mirror. Everything else differs by representation; the
sorts are representation-free, and the eventual translation carries them across by identity.
-/

namespace LambdaLab.CoC

/-- The two sorts: `*` (propositions/types of terms) and `□` (the sort of `*`). -/
inductive Srt where
  | prop
  | typ
  deriving DecidableEq, Repr

end LambdaLab.CoC
