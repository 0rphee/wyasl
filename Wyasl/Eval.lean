import Wyasl.LispVal

set_option diagnostics true
namespace Wyasl.Eval

open Wyasl.LispVal

unsafe def getVar (name : String) : Eval LispVal := do
  match (<- EvalT.read).get? name with
  | .some x => pure x
  | .none => throw <| .unboundVar name

mutual
def getEven : List t -> List t
  | [] => []
  | x :: xs => x :: getOdd xs

def getOdd : List t -> List t
  | [] => []
  | _ :: xs => getEven xs
end

unsafe def ensureAtom : LispVal -> Eval String
  | .atom n => pure (n)
  | v => throw <| .typeMismatch "atom" v

mutual
unsafe def evalBody : LispVal -> Eval LispVal
  | .list [.list [ .atom "define" , .atom var , defExpr ], rest] => do
    let evalVal <- eval defExpr
    withReader
      (fun env => env.insert var evalVal)
      (eval rest)
  | .list (.list [.atom "define", .atom var, defExpr] :: rest) => do
    let evalVal <- eval defExpr
    withReader
      (fun env => env.insert var evalVal)
      (evalBody (.list rest))
  | x => eval x

unsafe def applyLambda (expr : LispVal) (params : List String) (args : List LispVal) : Eval LispVal := do
  let argEval <- args.mapA eval
  withReader
    (fun env => env.insertMany (params.zip argEval))
    (eval expr)

unsafe def eval (lispVal : LispVal ) : Eval LispVal :=
  match lispVal with
  | .number _ | .string _ | .bool _ | .nil => pure lispVal
  | .atom n => getVar n
  | .list [.atom "quote", val] => pure val
  | .list (.atom "write" :: rest) =>
    (match rest with
    | last :: [] => last
    | _ => .list rest)
      |> showVal |> Std.Format.pretty |> .string |> pure
  | .list [.atom "if", pred, texpr, fexpr] => do
    match <- eval pred with
    | .bool true => eval texpr
    | .bool false => eval fexpr
    | _ => throw <| .badSpecialForm "if"
  | .list [.atom "let", .list pairs, expr] => do
    let atoms <- (getEven pairs).mapA ensureAtom
    let vals <- (getOdd pairs).mapA eval
    withReader
      (fun env => env.insertMany (atoms.zip vals))
      (evalBody expr)
  | .list [] => pure .nil
  | .list [.atom "lambda", .list params, expr] => do
    let envLocal <- read
    let paramAtoms <- params.mapA ensureAtom
    pure <| .lambda (applyLambda expr (paramAtoms) ) envLocal
  | .list (x :: xs) => do
    let funVar <- eval x
    let xVal <- xs.mapA eval
    match funVar with
    | .fn internalFn => internalFn xVal
    | .lambda internalFn boundEnv =>
      withReader
        (fun _ => boundEnv)
        (internalFn xVal)
    | _ => throw <| .notFunction funVar
  |  _ => throw <| .default lispVal
end
