import Std.Data.TreeMap

namespace Wyasl.LispVal

def EnvCtx a := Std.TreeMap String a

def Eval a := ReaderT (EnvCtx a) IO a

def Func a := List a -> Eval a 

unsafe inductive LispVal where
  | atom   : String -> LispVal
  | list   : List LispVal -> LispVal
  | number : Int64 -> LispVal
  | string : String -> LispVal
  | fn     : Func LispVal -> LispVal
  | lambda : Func LispVal -> EnvCtx LispVal -> LispVal
  | nil    : LispVal
  | bool   : Bool -> LispVal

unsafe def showVal : LispVal -> Std.Format
  | .atom a => .text a
  -- TODO: intersperse .list
  | .list a => "(" ++ List.foldl (fun x y => x ++ " "++  showVal y) "" a ++ ")"
  | .number a => repr a
  | .string a => repr a
  | .fn _ => "(internal function)"
  | .lambda _ _ => "(lambda function)"
  | .nil => "Nil"
  | .bool a =>
    match a with
    | true => "#t"
    | false => "#f"

export LispVal.LispVal (atom list number string fn lambda nil bool)
end Wyasl.LispVal
