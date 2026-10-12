-- This module serves as the root of the `LambdaLab` library.
-- Import modules here that should be built as part of the library.
import LambdaLab.Relation.Closure
import LambdaLab.Relation.Normalization
import LambdaLab.Languages.Stlc.DeBruijn.Basic
import LambdaLab.Languages.Stlc.DeBruijn.Typing
import LambdaLab.Languages.Stlc.DeBruijn.Step
import LambdaLab.Languages.Stlc.DeBruijn.MStep
import LambdaLab.Languages.Stlc.DeBruijn.Eval
import LambdaLab.Languages.Stlc.DeBruijn.Substitution
import LambdaLab.Languages.Stlc.DeBruijn.ParSubst
import LambdaLab.Languages.Stlc.DeBruijn.Reducibility
import LambdaLab.Languages.Stlc.DeBruijn.Properties
import LambdaLab.Languages.Stlc.DeBruijn.Preservation
import LambdaLab.Languages.Stlc.DeBruijn.Confluence
import LambdaLab.Languages.Stlc.Named.Basic
import LambdaLab.Languages.Stlc.Named.Step.Basic
import LambdaLab.Languages.Stlc.Named.Step.MStep
import LambdaLab.Languages.Stlc.Named.Alpha
import LambdaLab.Languages.Stlc.Named.Typing.Basic
import LambdaLab.Languages.Stlc.Named.Typing.Principality
import LambdaLab.Languages.Stlc.Named.Typing.Properties
import LambdaLab.Languages.Stlc.Named.Translation
import LambdaLab.Languages.Stlc.Named.Step.Confluence
import LambdaLab.Languages.Stlc.Named.Typing.Preservation
import LambdaLab.Languages.Stlc.Named.Typing.Normalization
import LambdaLab.Languages.Stlc.Named.Step.Eval
import LambdaLab.Languages.Stlc.Named.Typing.Unification
import LambdaLab.Languages.Stlc.Named.Typing.W
import LambdaLab.Languages.Stlc.Named.Typing.J
import LambdaLab.Languages.Stlc.Named.Typing.D
import LambdaLab.Languages.Stlc.Named.Typing.S
import LambdaLab.Languages.Stlc.Named.Typing.Target
import LambdaLab.Languages.SystemF.DeBruijn.Syntax
import LambdaLab.Languages.SystemF.DeBruijn.Typing
import LambdaLab.Languages.SystemF.DeBruijn.Reduction
import LambdaLab.Languages.SystemF.DeBruijn.Normalization
import LambdaLab.Languages.SystemF.DeBruijn.Check
import LambdaLab.Languages.SystemF.DeBruijn.Eval
import LambdaLab.Languages.SystemF.Named.Basic
import LambdaLab.Languages.SystemF.Named.Translation
import LambdaLab.Languages.SystemF.Named.Step
import LambdaLab.Languages.SystemF.Named.Typing
import LambdaLab.Languages.SystemF.Named.Alpha
import LambdaLab.Languages.SystemF.Named.Eval
import LambdaLab.Languages.SystemF.Surface
import LambdaLab.Languages.SystemF.Pipeline
import LambdaLab.Languages.CoC.DeBruijn.Syntax
import LambdaLab.Languages.CoC.DeBruijn.Reduction
import LambdaLab.Languages.CoC.DeBruijn.Confluence
import LambdaLab.Languages.CoC.DeBruijn.Typing
import LambdaLab.Languages.CoC.DeBruijn.Inversion
import LambdaLab.Languages.CoC.DeBruijn.Preservation
import LambdaLab.Languages.CoC.DeBruijn.Classification
import LambdaLab.Languages.CoC.DeBruijn.Normalization
import LambdaLab.Languages.CoC.DeBruijn.Eval
import LambdaLab.Languages.CoC.DeBruijn.Check
import LambdaLab.Languages.CoC.DeBruijn.Scope
import LambdaLab.Languages.CoC.Named.Basic
import LambdaLab.Languages.CoC.Named.Translation
import LambdaLab.Languages.CoC.Named.Step
import LambdaLab.Languages.CoC.Named.Typing
import LambdaLab.Languages.CoC.Named.Alpha
import LambdaLab.Languages.CoC.Named.Eval
import LambdaLab.Languages.CoC.Surface
import LambdaLab.Languages.CoC.Pipeline
import LambdaLab.Languages.CoIC.DeBruijn.Syntax
import LambdaLab.Languages.CoIC.DeBruijn.Reduction
import LambdaLab.Languages.CoIC.DeBruijn.Confluence
import LambdaLab.Languages.CoIC.DeBruijn.Typing
import LambdaLab.Languages.CoIC.DeBruijn.Inversion
import LambdaLab.Languages.CoIC.DeBruijn.Preservation
import LambdaLab.Languages.CoIC.DeBruijn.Classification
import LambdaLab.Languages.CoIC.DeBruijn.Normalization
import LambdaLab.Languages.CoIC.DeBruijn.Eval
import LambdaLab.Languages.CoIC.DeBruijn.Check
import LambdaLab.Languages.CoIC.DeBruijn.Scope


-- The parser stack, the categorical layer, the vernacular and the example languages.
--
-- These were previously outside the root, so `lake build` did not typecheck them and files
-- could (and did) rot undetected. Everything live is imported here now.
--
-- Deliberately excluded:
--   * Parser.IsoParser.Playground -- the prototype trail, kept as history. It is the only
--     unimported file in the tree; everything else here is built.
import LambdaLab.Parser.Numeral
import LambdaLab.Abstraction.Basic
import LambdaLab.Abstraction.Bicat
import LambdaLab.Abstraction.Chain
import LambdaLab.Abstraction.Parens
import LambdaLab.Abstraction.Tokenizer
import LambdaLab.Languages.Float.Decimal
import LambdaLab.Languages.Float.Pipeline
import LambdaLab.Nominal.Atom
import LambdaLab.Nominal.Basic
import LambdaLab.Nominal.Instances
import LambdaLab.Nominal.Substitution
import LambdaLab.Nominal.Unification.Subst
import LambdaLab.Nominal.Unification.Signature
import LambdaLab.Nominal.Unification.Bridge
import LambdaLab.Nominal.Unification.Measure
import LambdaLab.Nominal.Unification.Basic
import LambdaLab.Nominal.Unification.Soundness
import LambdaLab.Nominal.Unification.Completeness
import LambdaLab.Nominal.Unification.MGU
import LambdaLab.TypeSystem.Named.Context
import LambdaLab.TypeSystem.Named.Basic
import LambdaLab.TypeSystem.Intrinsic.Basic
import LambdaLab.TypeSystem.Named.Vernacular.Basic
import LambdaLab.TypeSystem.Named.Vernacular.Typing
import LambdaLab.TypeSystem.Named.Vernacular.Elaborate
import LambdaLab.TypeSystem.Named.Vernacular.Evaluate
import LambdaLab.Semantics.Walk
import LambdaLab.Pipeline.Basic
-- NB: `FreeName` lives in `TypeSystem/` but sits *above* `Pipeline.Basic`, since the atoms
-- it constructs are carved out of the grammar's reserved `Token`s. It is the one place the two
-- folders' layering is inverted.
import LambdaLab.TypeSystem.Named.FreeName
import LambdaLab.Pipeline.Def
import LambdaLab.Pipeline.Stages.Parse
import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.Pipeline.Stages.Evaluate
import LambdaLab.Pipeline.Compose
import LambdaLab.Pipeline.Cli
import LambdaLab.Languages.Trivial
import LambdaLab.NEList
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.IsoParser.Basic
import LambdaLab.Parser.IsoParser.Combinators
import LambdaLab.Parser.IsoParser.Example
import LambdaLab.Parser.IsoParser.Fix
import LambdaLab.Parser.IsoParser.Mixfix.Basic
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Complete
import LambdaLab.Parser.IsoParser.Mixfix.Exact
import LambdaLab.Parser.IsoParser.Mixfix.Parse
import LambdaLab.Parser.IsoParser.Mixfix.Sound
import LambdaLab.Parser.IsoParser.Mixfix.Tree
import LambdaLab.Parser.IsoParser.Mixfix.Unambiguity
import LambdaLab.Parser.IsoParser.Notation
import LambdaLab.Parser.IsoParser.Token
import LambdaLab.Parser.IsoParser.Tokenize
import LambdaLab.Parser.LossyParser.Basic
import LambdaLab.Parser.Truncation
import LambdaLab.Parser.Truncation.Mixfix
import LambdaLab.Languages.Stlc.Named.Pipeline
import LambdaLab.Languages.Stlc.Named.TypeSystem
import LambdaLab.Languages.Stlc.Named.Typing.JComplete
