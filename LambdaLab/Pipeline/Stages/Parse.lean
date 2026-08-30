import LambdaLab.Pipeline.Basic
import LambdaLab.Parser.IsoParser.Notation

/-!
# The vernacular biparser, derived — now lossy

A `Language` supplies two `LossyParser`s (`pTy`, `pTm`) and their annotation families.
*Everything* here is derived from them — the command parser, the file parser, the round-trip
proof, and (new) the `Abs` morphism.

**The derivation strategy.** The `IsoParser` combinator layer (`gdo`, `comap`, `tok`, `many1`)
is reused, not cloned: each lossy component crosses into it as an `IsoParser` over its
*annotated values* (`toIsoParser`, whose printed value is the index — definitionally), the
existing combinators assemble the grammar with the **annotated command/program as the source**,
and the assembled parser crosses back (`toLossyParserSigma`) once its printed value is shown to
be the index (`echo` — `rfl` after eta, plus one induction for `many1`).

So the seams are exactly the old ones — `pTy`'s FOLLOW is pinned to `:=`, `pTm`'s to `def`, and
every `gdo` obligation still discharges definitionally. What changed is only what flows through:
values are parsed, spellings are printed, and the annotation family records the difference.

**The payoff:** `Language.abstraction` — every plugged-in language yields an `Abs` morphism
`List Token ⇝ Program`, with the program's full surface spelling as the annotation.
-/

namespace LambdaLab.Pipeline

open LambdaLab.Parser.IsoParser
open LambdaLab.Parser.LossyParser (LossyParser)
open LambdaLab (Abstraction)

/-- An identifier: one token the language admits as a variable name. Aligned: source and value
are `Var L`, so a name the language would reject is unrepresentable. -/
def Language.pName (L : Language) :
    IsoParser Token (fun t => L.isVarName t = true) (fun _ => True) (Var L) (Var L) :=
  sat L.isVarName

/-! ## The command -/

/-- Everything a command's surface may spell beyond the command itself: the annotations of its
type and its term. (The name and the keywords have exactly one spelling.) -/
def Command.Ann (L : Language) : Command L → Type :=
  fun c => L.AnnTy c.ty × L.AnnTm c.tm

/-- The command parser at the `IsoParser` level: the **source is the annotated command**. The
type/term sub-parsers cross in via `toIsoParser` and `comap` the slice of the source they print
from; the one non-trivial seam — a type may be followed by `:=` — is definitionally true, as
before. -/
def Language.commandIso (L : Language) :
    IsoParser Token (· = kwDef) followDef (Σ c : Command L, Command.Ann L c) (Command L) := gdo
  let _kw ← tok kwDef
  let n ← comap (fun s => s.1.name) L.pName
  let _c ← tok kwColon
  let ty ← comap (fun s => ⟨s.1.ty, s.2.1⟩) L.pTy.toIsoParser
  let _a ← tok kwAssign
  let tm ← comap (fun s => ⟨s.1.tm, s.2.2⟩) L.pTm.toIsoParser
  return Command.decl n ty tm

/-- The command parser prints the value it is indexed by — each component's `print₁` is its
index, so the composite's is the reassembled command (eta). -/
theorem Language.commandIso_echo (L : Language) :
    ∀ s : Σ c : Command L, Command.Ann L c, (L.commandIso.print s).1 = s.1
  | ⟨.decl _ _ _, _⟩ => rfl

/-- **The command parser is exact**: whatever it consumed is the print of some annotated command.
Peel the five binds; the keyword and name slices have one spelling each, and the type and term
slices produce their annotations from the sub-parsers' own `exact` laws. -/
theorem Language.commandIso_exact (L : Language) : L.commandIso.Exact := by
  intro input b rest h
  obtain ⟨r, hp, hv⟩ := run_eq_some h
  obtain ⟨_kw, r₁, r₁', hTok, hp₂, he₁⟩ := bindParse_eq_some hp
  obtain ⟨n, r₂, r₂', hName, hp₃, he₂⟩ := bindParse_eq_some hp₂
  obtain ⟨_c, r₃, r₃', hColon, hp₄, he₃⟩ := bindParse_eq_some hp₃
  obtain ⟨tyv, r₄, r₄', hTy, hp₅, he₄⟩ := bindParse_eq_some hp₄
  obtain ⟨_a, r₅, r₅', hAssign, hp₆, he₅⟩ := bindParse_eq_some hp₅
  obtain ⟨tmv, hTm, hMap⟩ := map_parse_eq_some hp₆
  have hin : input = kwDef :: r₁.val := tokParse_eq_some hTok
  have hnm : r₁.val = n.val :: r₂.val := satParse_eq_some hName
  have hco : r₂.val = kwColon :: r₃.val := tokParse_eq_some hColon
  have has : r₄.val = kwAssign :: r₅.val := tokParse_eq_some hAssign
  obtain ⟨tyAnn, hTyAnn⟩ := L.pTy.exact r₃.val tyv r₄.val (by
    show (L.pTy.parse r₃.val).map (fun z => (z.1, z.2.val)) = some (tyv, r₄.val)
    rw [show L.pTy.parse r₃.val = some (tyv, r₄) from hTy]; rfl)
  obtain ⟨tmAnn, hTmAnn⟩ := L.pTm.exact r₅.val tmv r₅'.val (by
    show (L.pTm.parse r₅.val).map (fun z => (z.1, z.2.val)) = some (tmv, r₅'.val)
    rw [show L.pTm.parse r₅.val = some (tmv, r₅') from hTm]; rfl)
  have hrest : r₅'.val = rest := by rw [← he₅, ← he₄, ← he₃, ← he₂, ← he₁, hv]
  refine ⟨⟨Command.decl n tyv tmv, (tyAnn, tmAnn)⟩, ?_, ?_⟩
  · rw [L.commandIso_echo]
    exact hMap
  · show [kwDef] ++ ([n.val] ++ ([kwColon] ++ (L.pTy.print tyAnn
        ++ ([kwAssign] ++ L.pTm.print tmAnn)))) ++ rest = input
    rw [hin, hnm, hco, ← hTyAnn, has, ← hTmAnn, hrest]
    simp

/-- **The command parser, lossy**: value `Command L`, annotation `Command.Ann`. Canonical print
uses the sub-parsers' canonical annotations. -/
def Language.command (L : Language) :
    LossyParser Token (· = kwDef) followDef (Command L) (Command.Ann L) :=
  L.commandIso.toLossyParserSigma (fun {_} => (L.pTy.default, L.pTm.default))
    L.commandIso_echo L.commandIso_exact

/-! ## The program -/

/-- Annotations for every command of a list. -/
def ListAnn (L : Language) : List (Command L) → Type
  | [] => PUnit
  | c :: cs => Command.Ann L c × ListAnn L cs

/-- Annotations for every command of a program: the full surface spelling of a file. -/
def Program.Ann (L : Language) (prog : Program L) : Type :=
  Command.Ann L prog.1 × ListAnn L prog.2

def defaultListAnn (L : Language) : (cs : List (Command L)) → ListAnn L cs
  | [] => PUnit.unit
  | _ :: cs => ((L.pTy.default, L.pTm.default), defaultListAnn L cs)

/-- Zip a command list with its annotations into `many1`'s source shape. -/
def zipAnnList (L : Language) :
    (cs : List (Command L)) → ListAnn L cs → List (Σ c : Command L, Command.Ann L c)
  | [], _ => []
  | c :: cs, (a, as) => ⟨c, a⟩ :: zipAnnList L cs as

/-- Unzip `many1`'s source shape back into its commands — `zipAnnList`'s inverse, first half. -/
def unzipCmds (L : Language) : List (Σ c : Command L, Command.Ann L c) → List (Command L)
  | [] => []
  | s :: ss => s.1 :: unzipCmds L ss

/-- …and into their annotations — the second half. -/
def unzipAnns (L : Language) :
    (l : List (Σ c : Command L, Command.Ann L c)) → ListAnn L (unzipCmds L l)
  | [] => PUnit.unit
  | s :: ss => (s.2, unzipAnns L ss)

/-- Zipping undoes unzipping — what lets an exactness witness for `many1` (a list of annotated
commands) be reshaped into `parserIso`'s `Σ prog, Program.Ann` source. -/
theorem zipAnnList_unzip (L : Language) :
    ∀ l : List (Σ c : Command L, Command.Ann L c),
      zipAnnList L (unzipCmds L l) (unzipAnns L l) = l
  | [] => rfl
  | s :: ss => by
      show (⟨s.1, s.2⟩ : Σ c : Command L, Command.Ann L c)
          :: zipAnnList L (unzipCmds L ss) (unzipAnns L ss) = s :: ss
      rw [zipAnnList_unzip L ss]

/-- The file parser at the `IsoParser` level: the existing `many1` over `commandIso`, with the
source reshaped from `Σ prog, annotations` to `many1`'s list-of-`Σ`. A command's FIRST *is*
`def` and its FOLLOW *is* `def`, so the repetition obligation is the identity, as before. -/
def Language.parserIso (L : Language) :
    IsoParser Token (· = kwDef) (fun t => followDef t ∧ ¬ t = kwDef)
      (Σ prog : Program L, Program.Ann L prog) (NEList (Command L)) :=
  comap (fun s => (⟨s.1.1, s.2.1⟩, zipAnnList L s.1.2 s.2.2))
    (many1 L.commandIso (fun _ h => h))

/-- `many1`'s printed values over a zipped source are the original commands. -/
theorem Language.printV_zipAnnList (L : Language) :
    ∀ (cs : List (Command L)) (as : ListAnn L cs),
      many1PrintV L.commandIso (zipAnnList L cs as) = cs
  | [], _ => rfl
  | c :: cs, (a, as) => by
      simp only [zipAnnList, many1PrintV, L.printV_zipAnnList cs as,
        L.commandIso_echo ⟨c, a⟩]

/-- The file parser prints the program it is indexed by. -/
theorem Language.parserIso_echo (L : Language)
    (s : Σ prog : Program L, Program.Ann L prog) : (L.parserIso.print s).1 = s.1 := by
  show ((L.commandIso.print ⟨s.1.1, s.2.1⟩).1,
    many1PrintV L.commandIso (zipAnnList L s.1.2 s.2.2)) = s.1
  rw [L.commandIso_echo ⟨s.1.1, s.2.1⟩, L.printV_zipAnnList s.1.2 s.2.2]

/-- **The file parser is exact**: `many1`'s exactness from `commandIso_exact`, with the witness
(a list of annotated commands) unzipped into the `Σ prog, Program.Ann` source. -/
theorem Language.parserIso_exact (L : Language) : L.parserIso.Exact := by
  intro input b rest h
  obtain ⟨⟨s₀, ss⟩, hs1, hs2⟩ :=
    many1_exact (fun _ h => h) L.commandIso_exact input b rest h
  refine ⟨⟨⟨s₀.1, unzipCmds L ss⟩, (s₀.2, unzipAnns L ss)⟩, ?_, ?_⟩
  · show ((many1 L.commandIso (fun _ h => h)).print
        (⟨s₀.1, s₀.2⟩, zipAnnList L (unzipCmds L ss) (unzipAnns L ss))).1 = b
    rw [zipAnnList_unzip]
    exact hs1
  · show ((many1 L.commandIso (fun _ h => h)).print
        (⟨s₀.1, s₀.2⟩, zipAnnList L (unzipCmds L ss) (unzipAnns L ss))).2 ++ rest = input
    rw [zipAnnList_unzip]
    exact hs2

/-- **The file parser, lossy**: value `Program L` (as `NEList (Command L)`), annotation the full
surface spelling. Canonical print = every command in canonical form. -/
def Language.parser (L : Language) :
    LossyParser Token (· = kwDef) (fun t => followDef t ∧ ¬ t = kwDef)
      (NEList (Command L)) (Program.Ann L) :=
  L.parserIso.toLossyParserSigma
    (fun {prog} => ((L.pTy.default, L.pTm.default), defaultListAnn L prog.2))
    L.parserIso_echo L.parserIso_exact

/-- **The file round-trip.** Print a program under *any* spelling, parse it back, recover the
program exactly with nothing left over — for every language, no side-conditions. -/
theorem Language.parser_roundtrip (L : Language) (prog : Program L)
    (ann : Program.Ann L prog) :
    L.parser.run (L.parser.print ann) = some (prog, []) :=
  L.parser.roundtrip prog ann

/-! ## The printer's vocabulary

Everything the file printer emits is a vernacular keyword, a declaration name, or a token of one
of the two sub-printers. So a token outside all of those — the freshening stage's `_`, say — is
never printed, which is the obligation `Abstraction.restrict` asks for to put a stage in front
of the parser. -/

/-- The command printer's vocabulary: keywords, the name, the two sub-prints. -/
theorem command_print_not_mem (L : Language) {x : Token}
    (hdef : x ≠ kwDef) (hcolon : x ≠ kwColon) (hassign : x ≠ kwAssign)
    (hvar : L.isVarName x = false)
    (hty : ∀ {v : L.Ty} (a : L.AnnTy v), x ∉ L.pTy.print a)
    (htm : ∀ {v : L.Tm} (a : L.AnnTm v), x ∉ L.pTm.print a)
    (c : Command L) (a : Command.Ann L c) :
    x ∉ (L.commandIso.print ⟨c, a⟩).2 := by
  obtain ⟨n, τ, t⟩ := c
  show x ∉ [kwDef] ++ ([n.val] ++ ([kwColon] ++ (L.pTy.print a.1
    ++ ([kwAssign] ++ L.pTm.print a.2))))
  intro hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · exact hdef h
  · have hn := h.symm ▸ n.property
    rw [hvar] at hn
    simp at hn
  · exact hcolon h
  · exact hty a.1 h
  · exact hassign h
  · exact htm a.2 h

/-- …and the program printer's: every command's, concatenated. -/
theorem printOut_not_mem (L : Language) {x : Token}
    (hcmd : ∀ (c : Command L) (a : Command.Ann L c), x ∉ (L.commandIso.print ⟨c, a⟩).2) :
    ∀ (cs : List (Command L)) (as : ListAnn L cs),
      x ∉ many1PrintOut L.commandIso (zipAnnList L cs as)
  | [], _ => by simp [zipAnnList, many1PrintOut]
  | c :: cs, (a, as) => by
      rw [zipAnnList, many1PrintOut]
      intro hmem
      cases List.mem_append.mp hmem with
      | inl h => exact hcmd c a h
      | inr h => exact printOut_not_mem L hcmd cs as h

/-- **A token outside the printable vocabulary is never printed** — keywords, names, and the two
sub-printers' outputs are all there is. -/
theorem Language.parser_print_not_mem (L : Language) {x : Token}
    (hdef : x ≠ kwDef) (hcolon : x ≠ kwColon) (hassign : x ≠ kwAssign)
    (hvar : L.isVarName x = false)
    (hty : ∀ {v : L.Ty} (a : L.AnnTy v), x ∉ L.pTy.print a)
    (htm : ∀ {v : L.Tm} (a : L.AnnTm v), x ∉ L.pTm.print a)
    {prog : Program L} (ann : Program.Ann L prog) :
    x ∉ L.parser.print ann := by
  show x ∉ (L.commandIso.print ⟨prog.1, ann.1⟩).2
    ++ many1PrintOut L.commandIso (zipAnnList L prog.2 ann.2)
  intro hmem
  cases List.mem_append.mp hmem with
  | inl h =>
      exact command_print_not_mem L hdef hcolon hassign hvar hty htm prog.1 ann.1 h
  | inr h =>
      exact printOut_not_mem L
        (command_print_not_mem L hdef hcolon hassign hvar hty htm) prog.2 ann.2 h

/-- **Every language is an `Abs` morphism** `List Token ⇝ Program`: the whole-file abstraction,
whose annotation is the file's surface spelling. Composes with the tokenizer
(`Abstraction/Tokenizer.lean`) for the `List Char` pipeline. -/
def Language.abstraction (L : Language) :
    Abstraction (List Token) (NEList (Command L)) (Program.Ann L) :=
  L.parser.toAbstraction

end LambdaLab.Pipeline
