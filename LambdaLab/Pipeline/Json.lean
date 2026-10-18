/-!
# JSON, as much as a language server needs

A JSON value, a printer and a parser. Lean ships a JSON library, but it lives in the `Lean` package,
and importing any of that package links all of it: an executable goes from about 5 MB to about
150 MB. What the language server (`Pipeline/Lsp.lean`) needs is this much, so it is written here.

Numbers are integers: everything the protocol counts is a line, a character, an id or a version.
A fraction or an exponent is read and dropped.

This is plumbing, not part of the development: nothing is proved about it.
-/

namespace LambdaLab.Pipeline

/-- A JSON value. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving Inhabited

namespace Json

/-! ## Building and reading -/

def mkObj (kvs : List (String × Json)) : Json := .obj kvs.toArray

instance : Coe String Json := ⟨.str⟩
instance : Coe Bool Json := ⟨.bool⟩
instance : OfNat Json n := ⟨.num n⟩

/-- A field of an object. -/
def get? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def str? : Json → Option String
  | .str s => some s
  | _ => none

def int? : Json → Option Int
  | .num n => some n
  | _ => none

def arr? : Json → Option (Array Json)
  | .arr xs => some xs
  | _ => none

/-- A string field, through a path of objects. -/
def getStr? (j : Json) (path : List String) : Option String :=
  (path.foldlM (fun (j : Json) k => j.get? k) j).bind str?

/-! ## Printing -/

/-- Four hex digits. -/
def hex4 (n : Nat) : String :=
  let d (k : Nat) := "0123456789abcdef".toList.getD ((n / k) % 16) '0'
  String.ofList [d 4096, d 256, d 16, d 1]

/-- A string literal, escaped. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => if c.toNat < 0x20 then "\\u" ++ hex4 c.toNat else c.toString) ++ "\""

/-- Print compactly. -/
partial def render : Json → String
  | .null => "null"
  | .bool b => toString b
  | .num n => toString n
  | .str s => quote s
  | .arr xs => "[" ++ ",".intercalate (xs.toList.map render) ++ "]"
  | .obj kvs =>
      "{" ++ ",".intercalate (kvs.toList.map fun (k, v) => quote k ++ ":" ++ render v) ++ "}"

/-! ## Parsing -/

def skipWs : List Char → List Char
  | c :: cs => if c == ' ' || c == '\n' || c == '\r' || c == '\t' then skipWs cs else c :: cs
  | [] => []

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4? : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: r => do
      let x ← hexVal a; let y ← hexVal b; let z ← hexVal c; let w ← hexVal d
      pure (((x * 16 + y) * 16 + z) * 16 + w, r)
  | _ => none

/-- The rest of a string literal, after its opening quote. -/
partial def parseStr (acc : Array Char) : List Char → Option (String × List Char)
  | '"' :: r => some (String.ofList acc.toList, r)
  | '\\' :: c :: r =>
      match c with
      | '"' => parseStr (acc.push '"') r
      | '\\' => parseStr (acc.push '\\') r
      | '/' => parseStr (acc.push '/') r
      | 'b' => parseStr (acc.push (Char.ofNat 8)) r
      | 'f' => parseStr (acc.push (Char.ofNat 12)) r
      | 'n' => parseStr (acc.push '\n') r
      | 'r' => parseStr (acc.push '\r') r
      | 't' => parseStr (acc.push '\t') r
      | 'u' => do
          let (u, r) ← hex4? r
          if 0xD800 ≤ u && u < 0xDC00 then
            match r with
            | '\\' :: 'u' :: r' => do
                let (v, r'') ← hex4? r'
                parseStr (acc.push (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00)))) r''
            | _ => parseStr (acc.push (Char.ofNat 0xFFFD)) r
          else parseStr (acc.push (Char.ofNat u)) r
      | _ => none
  | c :: r => parseStr (acc.push c) r
  | [] => none

/-- A number; only its integer part is kept. -/
def parseNum (cs : List Char) : Option (Json × List Char) :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let digits := cs.takeWhile Char.isDigit
  if digits.isEmpty then none
  else
    let n : Nat := digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    let rest := (cs.drop digits.length).dropWhile fun c =>
      c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'
    some (.num (if neg then -(n : Int) else n), rest)

mutual
/-- A value, and what follows it. -/
partial def parseValue (cs : List Char) : Option (Json × List Char) :=
  match skipWs cs with
  | 'n' :: 'u' :: 'l' :: 'l' :: r => some (.null, r)
  | 't' :: 'r' :: 'u' :: 'e' :: r => some (.bool true, r)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => some (.bool false, r)
  | '"' :: r => (parseStr #[] r).map fun (s, r) => (.str s, r)
  | '[' :: r =>
      match skipWs r with
      | ']' :: r => some (.arr #[], r)
      | _ => parseElems #[] r
  | '{' :: r =>
      match skipWs r with
      | '}' :: r => some (.obj #[], r)
      | _ => parseFields #[] r
  | cs => parseNum cs

/-- The elements of an array, after its `[`. -/
partial def parseElems (acc : Array Json) (cs : List Char) : Option (Json × List Char) := do
  let (v, r) ← parseValue cs
  match skipWs r with
  | ',' :: r => parseElems (acc.push v) r
  | ']' :: r => pure (.arr (acc.push v), r)
  | _ => none

/-- The fields of an object, after its `{`. -/
partial def parseFields (acc : Array (String × Json)) (cs : List Char) :
    Option (Json × List Char) := do
  match skipWs cs with
  | '"' :: r =>
      let (k, r) ← parseStr #[] r
      match skipWs r with
      | ':' :: r =>
          let (v, r) ← parseValue r
          match skipWs r with
          | ',' :: r => parseFields (acc.push (k, v)) r
          | '}' :: r => pure (.obj (acc.push (k, v)), r)
          | _ => none
      | _ => none
  | _ => none
end

/-- Parse a whole JSON text. -/
def parse (s : String) : Option Json :=
  match parseValue s.toList with
  | some (j, r) => if (skipWs r).isEmpty then some j else none
  | none => none

end Json

end LambdaLab.Pipeline
