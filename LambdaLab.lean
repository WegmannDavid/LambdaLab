-- This module serves as the root of the `LambdaLab` library.
-- Import modules here that should be built as part of the library.
import LambdaLab.Relation.Closure
import LambdaLab.Relation.Normalization
import LambdaLab.Stlc.DeBruijn.Basic
import LambdaLab.Stlc.DeBruijn.Typing.Unification
import LambdaLab.Stlc.DeBruijn.TypeSystem
import LambdaLab.Stlc.DeBruijn.Typing.Basic
import LambdaLab.Stlc.DeBruijn.Step.Basic
import LambdaLab.Stlc.DeBruijn.Step.MStep
import LambdaLab.Stlc.DeBruijn.Step.Eval
import LambdaLab.Stlc.DeBruijn.Substitution
import LambdaLab.Stlc.DeBruijn.ParSubst
import LambdaLab.Stlc.DeBruijn.Typing.Reducibility
import LambdaLab.Stlc.DeBruijn.Typing.Properties
import LambdaLab.Stlc.DeBruijn.Typing.Preservation
import LambdaLab.Stlc.DeBruijn.Step.Confluence
import LambdaLab.Stlc.Named.Basic
import LambdaLab.Stlc.Named.Step.Basic
import LambdaLab.Stlc.Named.Step.MStep
import LambdaLab.Stlc.Named.Alpha
import LambdaLab.Stlc.Named.Typing.Basic
import LambdaLab.Stlc.Named.Typing.Principality
import LambdaLab.Stlc.Named.Typing.Properties
import LambdaLab.Stlc.Named.Translation
import LambdaLab.Stlc.Named.Step.Confluence
import LambdaLab.Stlc.Named.Typing.Preservation
import LambdaLab.Stlc.Named.Typing.Normalization
import LambdaLab.Stlc.Named.Step.Eval
import LambdaLab.Stlc.Named.Typing.Unification
import LambdaLab.Stlc.Named.Typing.W
import LambdaLab.Stlc.Named.Typing.J
import LambdaLab.Stlc.Named.Typing.D
import LambdaLab.Stlc.Named.Typing.S
import LambdaLab.Stlc.Named.Typing.Target


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
import LambdaLab.Abstraction.Freshen
import LambdaLab.Abstraction.Parens
import LambdaLab.Abstraction.Tokenizer
import LambdaLab.Arith.Pipeline
import LambdaLab.Inductive.Basic
import LambdaLab.Inductive.Example
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
import LambdaLab.TypeSystem.DeBruijn.Context
import LambdaLab.TypeSystem.DeBruijn.Basic
import LambdaLab.TypeSystem.Named.Vernacular.Basic
import LambdaLab.TypeSystem.Named.Vernacular.Typing
import LambdaLab.TypeSystem.Named.Vernacular.Elaborate
import LambdaLab.TypeSystem.Named.Vernacular.Evaluate
import LambdaLab.Pipeline.Basic
-- NB: `FreeName` lives in `TypeSystem/` but sits *above* `Pipeline.Basic`, since the atoms
-- it constructs are carved out of the grammar's reserved `Token`s. It is the one place the two
-- folders' layering is inverted.
import LambdaLab.TypeSystem.Named.FreeName
import LambdaLab.Pipeline.Stages.Parse
import LambdaLab.Pipeline.Stages.Elaborate
import LambdaLab.Pipeline.Stages.Evaluate
import LambdaLab.Pipeline.Compose
import LambdaLab.Pipeline.Cli
import LambdaLab.Pipeline.Example
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
import LambdaLab.Stlc.Named.Pipeline
import LambdaLab.Stlc.Named.TypeSystem
import LambdaLab.Stlc.Named.Typing.JComplete
