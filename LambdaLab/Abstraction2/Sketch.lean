import LambdaLab.Abstraction.Basic

def isSep (c : Char) : Bool := c.isWhitespace

--nonempty string that doesn't contain any separators
def Token : Type := sorry

--nonempty list of seperators
def NeSeperation : Type := sorry

--possibly empty list of seperators
def Seperation : Type := sorry


--redundant but hopefully convinient annotation type
inductive Seperators : List Token → Type where
| nil : Seperation → Seperators []
| cons : Seperation → (t : Token) → NeSeperation → Seperators (t :: ts)

def tokenize : Abstraction (List Char) (List Token) Seperators := sorry

-- a toy language that consists of a single variable with a possibly empty (_)
-- type annotation that is also just a token possibly wrapped in arbitrarily many redundant parentheses
inductive ExprWithParens where
| varWithType : Token → Token → ExprWithParens
| parens : ExprWithParens → ExprWithParens

--a single type called * exists in this toy language
def Star : Token := sorry
-- we can instruct the compiler to infer this type by writing the token _
def Infer : Token := sorry

inductive ExprWithoutParens where
| var : Token → Token → ExprWithoutParens

inductive ParensAnnotation : ExprWithoutParens → Type where
| var : (tm : Token) → (ty : Token) → ParensAnnotation (ExprWithoutParens.var tm ty)
| parens : ParensAnnotation e → ParensAnnotation e

def fromAnnotation : ParensAnnotation e → ExprWithParens
| ParensAnnotation.var tm ty => ExprWithParens.varWithType tm ty
| ParensAnnotation.parens a => ExprWithParens.parens (fromAnnotation a)

def parse : Abstraction (List Token) ExprWithoutParens ParensAnnotation := sorry

inductive Typing : ExprWithoutParens → Prop where
| var : Typing (ExprWithoutParens.var tm Star)

def TypedExpr : Type := { e : ExprWithoutParens // Typing e }

inductive TypingAnnotation : TypedExpr → Type where
| annotated : TypingAnnotation ⟨ExprWithoutParens.var tm Star, Typing.var⟩
| infer : TypingAnnotation ⟨ExprWithoutParens.var tm Star, Typing.var⟩

def fromTypingAnnotation : TypingAnnotation e → ExprWithoutParens
| @TypingAnnotation.annotated tm => ExprWithoutParens.var tm Star
| @TypingAnnotation.infer tm => ExprWithoutParens.var tm Infer

def typeCheck : Abstraction ExprWithoutParens TypedExpr (fun e => Unit) := sorry


-- full pipeline:
-- tokenize then parse then type check
def pipeline : Abstraction (List Char) TypedExpr sorry := sorry
