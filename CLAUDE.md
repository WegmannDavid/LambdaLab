# LambdaLab

Lean 4 formalization. STLC (named + de Bruijn variants), a mixfix parser
and vernacular layer, and first-order unification.

## Git workflow

- Commit autonomously when a logical unit of work is complete and
  `lake build` passes. Don't wait to be asked.
- Stage only files relevant to the unit of work. Never `git add -A` /
  `git add .` — unrelated working-tree changes (e.g. half-finished work
  in another module) must stay out of the commit.
- Push autonomously to feature branches. Confirm before pushing to
  `main` or any branch that other people or CI consume.
- Never force-push, skip hooks (`--no-verify`), or amend already-pushed
  commits without explicit approval.
- Branch names should be descriptive of the work, not generic.

## Build

`lake build` from the project root builds the whole library. Individual
modules: `lake build LambdaLab.Unification.Basic` (etc.).
