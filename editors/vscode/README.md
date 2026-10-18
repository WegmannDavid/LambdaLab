# LambdaLab for VS Code

Syntax highlighting and live checking for the LambdaLab calculi: `.stlc`, `.sf` (System F), `.coc`,
`.coic`, `.ecc`, `.float`.

Each language's compiler is also its language server (`stlc --lsp`, …). The extension starts the
compiler from the workspace's `.lake/build/bin` (or the directory in the `lambdalab.serverDirectory`
setting), so build the compilers first:

    lake build stlc systemf coc coic ecc float

What it gives you, in any of the six languages:

* errors as you type — every error in the file, each at its declaration;
* the outline (Outline view, breadcrumbs, Go to Symbol): every declaration;
* Format Document: the canonical layout, which by the parser's round-trip law cannot change what the
  file means;
* colours, from a TextMate grammar per language (`syntaxes/generate.py` writes them).
* Unicode input, Lean's: `\lam` → λ, `\Pi` → Π, `\to` → →, `\star` → ⋆, `\square` → □,
  `\forall` → ∀, `\Lambda` → Λ, and every other abbreviation Lean knows. This is the Lean
  extension's input mode, switched on for these languages (the `lean4.input.languages` setting) —
  so it needs the Lean 4 extension installed.

After rebuilding a compiler, run **LambdaLab: Restart Language Servers**.

## Install

No Node.js needed — the client has no dependencies, and packaging is a Python script:

    python3 package.py
    code --install-extension lambdalab-*.vsix
