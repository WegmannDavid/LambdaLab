import LambdaLab.Language.Parser

/-!
# Verified type-checking for vernacular programs

`Decl.check` takes a parsed declaration and returns either an error or a
proof that its body has the declared type.

`Program.check` threads a context through a list of commands:
* `def NAME : TYPE := BODY` — checks `BODY` against `TYPE`, then extends
  the context with `NAME : TYPE` for the commands that follow.
* `eval BODY` / `check BODY` — infer `BODY`'s type in the current
  context; do not extend it.

The successful result of `Program.check` is a `CheckedProgram` — a
heterogeneously-indexed list pairing each command with the data its
runtime semantics needs (a `HasType` derivation).
-/

namespace LambdaLab.Language

/-- A *typing claim* under a substitution: a `σ : Subst L.Ty` plus a
`HasType` derivation about the `σ`-substituted triple `(Γ, e, τ)`. This
is what every successful check produces; for the kernel checker `σ = ∅`. -/
abbrev TypingClaim (L : Language) (Γ : Context L.Ty)
    (e : L.Term) (τ : L.Ty) : Type :=
  Σ' σ : Subst L.Ty,
    L.HasType (HasSubst.pSubst Γ σ)
              (HasSubst.pSubst e σ)
              (HasSubst.pSubst τ σ)

/-! ## Per-declaration errors and result -/

/-- Why a single declaration failed to type-check. -/
inductive DeclError (Ty : Type) where
  /-- Inference itself failed (unbound variable, applied non-function,
  argument-type mismatch). -/
  | inferError : TypeError Ty → DeclError Ty
  /-- Inference succeeded but the inferred type doesn't match the
  declared one. -/
  | typeMismatch : (declared inferred : Ty) → DeclError Ty

/-- Result of checking one declaration: an error, or a typing claim
that the body matches the declared type. -/
inductive Decl.CheckResult (L : Language) (Γ : Context L.Ty) (d : Decl L) :
    Type where
  | error : DeclError L.Ty → Decl.CheckResult L Γ d
  | ok    : TypingClaim L Γ d.body d.type → Decl.CheckResult L Γ d

/-- Type-check one declaration in context `Γ`. On success, the result
carries σ and a `HasType` derivation about the σ-substituted triple. -/
def Decl.check (L : Language) (Γ : Context L.Ty) (d : Decl L) :
    Decl.CheckResult L Γ d :=
  match L.elaborate Γ d.body with
  | .error err => .error (.inferError err)
  | .ok τ σ proof _mgu =>
      if h : τ = d.type then
        .ok ⟨σ, h ▸ proof⟩
      else
        .error (.typeMismatch d.type τ)

/-! ## Per-command errors -/

/-- Why a single command failed to check. -/
inductive CommandError (Ty : Type) where
  /-- A `def NAME ...` command failed; carries the declaration's name
  and the reason. -/
  | inDecl  : (declName : String) → DeclError Ty → CommandError Ty
  /-- An `eval` command's body failed to infer a type. -/
  | inEval  : TypeError Ty → CommandError Ty
  /-- A `check` command's body failed to infer a type. -/
  | inCheck : TypeError Ty → CommandError Ty

/-! ## Program-level checking -/

/-- A type-checked vernacular command, paired with the data needed to
run it: a `HasType` derivation in the appropriate context. -/
inductive CheckedCommand (L : Language) (Γ : Context L.Ty) :
    Command L → Type where
  | decl  : (d : Decl L) →
            TypingClaim L Γ d.body d.type →
            CheckedCommand L Γ (.decl d)
  | eval  : (e : L.Term) → (τ : L.Ty) →
            TypingClaim L Γ e τ →
            CheckedCommand L Γ (.eval e)
  | check : (e : L.Term) → (τ : L.Ty) →
            TypingClaim L Γ e τ →
            CheckedCommand L Γ (.check e)

/-- Context update induced by a command: `decl` extends the context
with the declared name; `eval`/`check` leave it unchanged. -/
def Command.afterCtx {L : Language} (Γ : Context L.Ty) :
    Command L → Context L.Ty
  | .decl d  => Γ.cons d.name d.type
  | .eval _  => Γ
  | .check _ => Γ

/-- A type-checked program: a list of `CheckedCommand`s with the
context threaded through `decl` commands. -/
inductive CheckedProgram (L : Language) :
    Context L.Ty → List (Command L) → Type where
  | nil {Γ : Context L.Ty} : CheckedProgram L Γ []
  | cons {Γ : Context L.Ty} {rest : List (Command L)}
         {c : Command L}
         (cc : CheckedCommand L Γ c)
         (tail : CheckedProgram L (Command.afterCtx Γ c) rest) :
      CheckedProgram L Γ (c :: rest)

/-- A program-level error: a per-command reason. -/
inductive ProgramError (Ty : Type) where
  | atCommand : CommandError Ty → ProgramError Ty

/-- Result of checking a program: a fully-checked program (with
derivations) or an error. -/
inductive Program.CheckResult (L : Language)
    (Γ : Context L.Ty) (cmds : List (Command L)) : Type where
  | error : ProgramError L.Ty → Program.CheckResult L Γ cmds
  | ok    : CheckedProgram L Γ cmds → Program.CheckResult L Γ cmds

/-- Type-check a list of commands, threading the context. -/
def Program.check (L : Language) :
    (Γ : Context L.Ty) → (cmds : List (Command L)) →
    Program.CheckResult L Γ cmds
  | _, []                  => .ok .nil
  | Γ, .decl d :: rest    =>
      match Decl.check L Γ d with
      | .error err => .error (.atCommand (.inDecl d.name err))
      | .ok claim  =>
          match Program.check L (Γ.cons d.name d.type) rest with
          | .error err => .error err
          | .ok tail   => .ok (.cons (.decl d claim) tail)
  | Γ, .eval e :: rest    =>
      match L.elaborate Γ e with
      | .error err           => .error (.atCommand (.inEval err))
      | .ok τ σ proof _mgu   =>
          match Program.check L Γ rest with
          | .error err => .error err
          | .ok tail   => .ok (.cons (.eval e τ ⟨σ, proof⟩) tail)
  | Γ, .check e :: rest   =>
      match L.elaborate Γ e with
      | .error err           => .error (.atCommand (.inCheck err))
      | .ok τ σ proof _mgu   =>
          match Program.check L Γ rest with
          | .error err => .error err
          | .ok tail   => .ok (.cons (.check e τ ⟨σ, proof⟩) tail)

/-- Closed-program entry point: check from the empty context. -/
def Program.checkClosed (L : Language) (cmds : List (Command L)) :
    Program.CheckResult L Context.empty cmds :=
  Program.check L Context.empty cmds

end LambdaLab.Language
