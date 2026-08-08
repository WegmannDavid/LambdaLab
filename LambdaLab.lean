-- This module serves as the root of the `LambdaLab` library.
-- Import modules here that should be built as part of the library.
import LambdaLab.Stlc.DeBruijn.Basic
import LambdaLab.Stlc.DeBruijn.Typing
import LambdaLab.Stlc.DeBruijn.Step
import LambdaLab.Stlc.DeBruijn.MStep
import LambdaLab.Stlc.DeBruijn.Eval
import LambdaLab.Stlc.DeBruijn.Substitution
import LambdaLab.Stlc.DeBruijn.ParSubst
import LambdaLab.Stlc.DeBruijn.Reducibility
import LambdaLab.Stlc.DeBruijn.Properties
import LambdaLab.Stlc.DeBruijn.Preservation
import LambdaLab.Stlc.DeBruijn.Confluence
import LambdaLab.Stlc.Named.Basic
import LambdaLab.Stlc.Named.Step.Basic
import LambdaLab.Stlc.Named.Step.MStep
import LambdaLab.Stlc.Named.Typing.Basic
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
import LambdaLab.Substitution.Basic
import LambdaLab.Substitution.Unification.Signature
import LambdaLab.Substitution.Unification.Bridge
import LambdaLab.Substitution.Unification.Measure
import LambdaLab.Substitution.Unification.Basic
import LambdaLab.Substitution.Unification.Soundness
import LambdaLab.Substitution.Unification.Completeness
import LambdaLab.Substitution.Unification.MGU


-- The parser stack, the categorical layer, the vernacular and the example languages.
--
-- These were previously outside the root, so `lake build` did not typecheck them and files
-- could (and did) rot undetected. Everything live is imported here now.
--
-- Deliberately excluded:
--   * Playground.*, Parser.IsoParser.Playground -- the prototype trail, kept as history.
import LambdaLab.Parser.Numeral
import LambdaLab.Abstraction.Basic
import LambdaLab.Abstraction.Bicat
import LambdaLab.Abstraction.Parens
import LambdaLab.Abstraction.Tokenizer
import LambdaLab.Arith.Pipeline
import LambdaLab.Inductive.Basic
import LambdaLab.Inductive.Example
import LambdaLab.TypeSystem.NameAlphabet
import LambdaLab.TypeSystem.Context
import LambdaLab.TypeSystem.Basic
import LambdaLab.Pipeline.Basic
-- NB: `FreeName` lives in `TypeSystem/` but sits *above* `Pipeline.Basic`, since the alphabet
-- it constructs is carved out of the grammar's reserved `Token`s. It is the one place the two
-- folders' layering is inverted.
import LambdaLab.TypeSystem.FreeName
import LambdaLab.Pipeline.Elaboratable
import LambdaLab.Pipeline.Typing
import LambdaLab.Pipeline.ElabStage
import LambdaLab.Pipeline.Biparser
import LambdaLab.Pipeline.Example
import LambdaLab.Pipeline.Pipeline
import LambdaLab.Pipeline.Vernacular
import LambdaLab.NEList
import LambdaLab.Parser.IsoParser.Adapters
import LambdaLab.Parser.IsoParser.Basic
import LambdaLab.Parser.IsoParser.Combinators
import LambdaLab.Parser.IsoParser.Example
import LambdaLab.Parser.IsoParser.Fix
import LambdaLab.Parser.IsoParser.Mixfix.Basic
import LambdaLab.Parser.IsoParser.Mixfix.Biparser
import LambdaLab.Parser.IsoParser.Mixfix.Complete
import LambdaLab.Parser.IsoParser.Mixfix.Parse
import LambdaLab.Parser.IsoParser.Mixfix.Sound
import LambdaLab.Parser.IsoParser.Mixfix.Tree
import LambdaLab.Parser.IsoParser.Notation
import LambdaLab.Parser.IsoParser.Token
import LambdaLab.Parser.IsoParser.Tokenize
import LambdaLab.Parser.LossyParser.Basic
import LambdaLab.Parser.Truncation
import LambdaLab.Parser.Truncation.Mixfix
import LambdaLab.Stlc.Named.Pipeline
import LambdaLab.Stlc.Named.TypeSystem
