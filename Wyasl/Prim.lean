import Wyasl.LispVal

namespace Wyasl.Prim

open Wyasl.LispVal


unsafe def mkF : (List LispVal -> Eval LispVal) -> LispVal := .fn 

unsafe abbrev Unary := LispVal -> Eval LispVal
unsafe abbrev Binary := LispVal -> LispVal -> Eval LispVal

inductive OpArgs where
  | unary
  | binary

unsafe def OpArgs.toFunType : OpArgs -> Type
  | .unary => Unary
  | .binary => Binary

unsafe def OpArgs.toInt64 : OpArgs -> Int64
  | .unary => 1
  | .binary => 2

unsafe def OpArgs.opMk (n : OpArgs) (op : n.toFunType) (args : List LispVal) : Eval LispVal :=
  match n, args with
  | .binary, [a, b] => op a b
  | .unary, [x] => op x
  | _ , _ => throw $ .numArgs n.toInt64  args

unsafe def fileExists (val : LispVal) : Eval LispVal :=
  match val with
  | .string txt => .bool <$> (System.FilePath.pathExists txt)
  | _ => throw <| .typeMismatch "read expects string, instead it got: " val

unsafe def wFileSlurp (fileName : String) : Eval LispVal := do
  if (<- System.FilePath.pathExists fileName)
  then .string <$> IO.FS.readFile fileName
  else throw <| .ioError s!" file does not exist {fileName}"

unsafe def slurp (val : LispVal) : Eval LispVal :=
  match val with
  | .string txt => wFileSlurp txt
  | _ => throw <| .typeMismatch "read expects string, instead it got: " val

-- wSlurp (openUrl) unimplemented

unsafe def putTextFile (filename : String) (msg : String) : Eval LispVal := do
  if <- System.FilePath.pathExists filename
  then IO.FS.writeFile filename msg *> pure (.string msg)
  else throw <| .ioError s!" file does not exist {filename}"

unsafe def put (file : LispVal) (msg : LispVal) : Eval LispVal :=
  match file, msg with
  | .string fileS, .string msgS => putTextFile fileS msgS
  | .string _, _ => throw <| .typeMismatch "put expects string in the second argument (try using show), instead got:" msg
  | _,  _ => throw <| .typeMismatch "put expects string, instead got:" file

unsafe def binopFold (binop : Binary) (farg : LispVal) (args : List LispVal) : Eval LispVal :=
  match args with
  | [] => throw <| .numArgs 2 args
  | [a, b] => binop a b
  | _ :: _ => List.foldlM binop farg args

unsafe def numBool (op : Int64 -> Bool) (val : LispVal) : Eval LispVal :=
  match val with
  | .number x => pure <| .bool (op x)
  | _ => throw <| .typeMismatch "numeric op" val

unsafe def numOp (op : Int64 -> Int64 -> Int64) (x : LispVal) (y : LispVal) : Eval LispVal :=
  match x, y with
  | .number vx, .number vy => pure <| .number (op vx vy)
  | .nil, .number _ => pure y
  | .number _, .nil => pure x
  | .number _, _ => throw $ .typeMismatch "numeric op" y
  | _, _ => throw $ .typeMismatch "numeric op" x

unsafe def strOp (op : String -> String -> String) (x : LispVal) (y : LispVal) : Eval LispVal :=
  match x, y with
  | .string vx, .string vy => pure <| .string (op vx vy)
  | .nil, .string _ => pure y
  | .string _, .nil => pure x
  | .string _, _ => throw $ .typeMismatch "string op " y
  | _, _ => throw $ .typeMismatch "string op" x

unsafe def eqOp (op : Bool -> Bool -> Bool) (x : LispVal) (y : LispVal) : Eval LispVal :=
  match x, y with
  | .bool vx, .bool vy => pure $ .bool (op vx vy)
  | .nil, .bool _ => pure y
  | .bool _, .nil => pure x
  | .bool _, _ => throw $ .typeMismatch "bool op " y
  | _, _ => throw $ .typeMismatch "bool op" x

unsafe def numCmp (op : Int64 -> Int64 -> Bool) (x : LispVal) (y : LispVal) : Eval LispVal :=
  match x, y with
  | .number vx, .number vy => pure <| .bool (op vx vy)
  | .nil, .number _ => pure y
  | .number _, .nil => pure x
  | .number _, _ => throw $ .typeMismatch "numeric op " y
  | _, _ => throw $ .typeMismatch "numeric op " x

unsafe def notOp (x : LispVal) : Eval LispVal :=
  match x with
  | .bool v => .pure <| .bool (not v)
  | _ => throw $ .typeMismatch "not expects Bool" x

unsafe def eqCmd (x : LispVal) (y : LispVal) : Eval LispVal :=
  match x, y with
  | .atom vx, .atom vy => pure <| .bool (vx == vy)
  | .number vx, .number vy => pure <| .bool (vx == vy)
  | .string vx, .string vy => pure <| .bool (vx == vy)
  | .bool vx, .bool vy => pure <| .bool (vx == vy)
  | .nil, .nil => pure <| .bool true
  | _, _ => pure <| .bool false


unsafe def cons (l : List LispVal) : Eval LispVal :=
  match l with
  | [x, .list yList] => .pure <| .list (x :: yList)
  | [_, _] => .pure (.list l)
  | _ => throw $ .expectedList "cons, in second argument"

unsafe def car (l : List LispVal) : Eval LispVal :=
  match l with
  | [.list []] | [] => pure .nil
  | [.list (x :: _)] => pure x
  | _ => throw $ .expectedList "car"

unsafe def cdr (l : List LispVal) : Eval LispVal :=
  match l with
  | [.list []] | [] => pure .nil
  | [.list (_ :: xs)] => pure (.list xs)
  | _ => throw $ .expectedList "cdr"

unsafe def quote (l : List LispVal) : Eval LispVal :=
  match l with
  | [.list xs] => pure <| .list (.atom "qoute" :: xs)
  | [_] => pure <| .list (.atom "quote" :: l)
  | _ => throw $ .numArgs 1 l

unsafe def binop := OpArgs.binary.opMk 
unsafe def unop :=  OpArgs.unary.opMk

def even (x : Int64) : Bool := (Int64.mod x 2) == 0
def odd (x : Int64) : Bool := not <| even x

unsafe def display : LispVal -> Eval LispVal
  | .string s => IO.println s *> pure .nil
  | v => throw $ .typeMismatch "display expects string, instead it got:"  v

unsafe def primEnv : EnvCtx LispVal :=
  Std.TreeMap.ofArray
    #[
      ("+", mkF $ binopFold (numOp (.+.)) (.number 0) )
    , ("*", mkF $ binopFold (numOp (.*.)) (.number 1) )
    , ("string-append", mkF $ binopFold (strOp (.++.)) (.string ""))
    , ("-", mkF $ binop $ numOp (.-.))
    , ("<", mkF $ binop $ numCmp (.<.))
    , ("<=", mkF $ binop $ numCmp (.<=.))
    , (">", mkF $ binop $ numCmp (.>.))
    , (">=", mkF $ binop $ numCmp (.>=.))
    , ("==", mkF $ binop $ numCmp (.==.))
    , ("even?", mkF $ unop $ numBool even)
    , ("odd?", mkF $ unop $ numBool odd)
    , ("neg?", mkF $ unop $ numBool (.< 0))
    , ("pos?", mkF $ unop $ numBool (.> 0))
    , ("eq?", mkF $ binop eqCmd )
    , ("null?", mkF $ unop (eqCmd .nil) )
    , ("bl-eq?", mkF $ binop $ eqOp (.==.))
    , ("and", mkF $ binopFold (eqOp (.&&.)) (.bool .true))
    , ("or", mkF $ binopFold (eqOp (.||.)) (.bool .false))
    , ("not", mkF $ unop notOp)
    , ("cons", mkF Prim.cons)
    , ("cdr", mkF Prim.cdr)
    , ("car", mkF Prim.car)
    , ("quote", mkF quote)
    , ("file?", mkF $ unop fileExists)
    , ("slurp", mkF $ unop slurp)
    -- , ("wslurp", mkF $ unop wSlurp)
    , ("put", mkF $ binop put)
    -- , ("read" ,mkF $ unop readFn)
    -- , ("parse", mkF $ unop parseFn)
    -- , ("eval", mkF $ unop eval)
    , ("show", mkF $ unop (pure ∘ .string ∘ Std.Format.pretty ∘ LispVal.showVal))
    , ("display", mkF $ unop display)
    ]
