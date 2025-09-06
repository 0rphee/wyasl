import Wyasl.LispVal
import Wyasl.Parser
import Wyasl.Prim

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
  | .list [.list [.atom "define" , .atom var , defExpr ], rest] => do
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
  | (.list [.atom "begin", rest]) => evalBody rest
  | (.list (.atom "begin" :: rest )) => evalBody $ .list rest
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

unsafe def parseWithoutLib (inp : String ) : Eval LispVal := do
  let expr <- Parser.WParser.readExprFile inp
  match expr with
  | .ok _ v => pure $ v
  | .error _ e => throw $ .pError (toString e) 

unsafe def parseWithLib (stdinput : String) (inp : String ) : Eval LispVal := do
  let stdlib <- Parser.WParser.readExprFile stdinput
  let expr <- Parser.WParser.readExpr inp
  match stdlib, expr with
  | .ok _ s, .ok _ e => endOfList s e
  | .error _ e, _ | _, .error _ e => throw $ .pError $ ToString.toString e
  where
    endOfList : LispVal -> LispVal -> Eval LispVal 
      | .list x, expr => pure $ .list $ x ++ [expr]
      | n, _ => throw $ .typeMismatch "failure to get variable: " n

unsafe def runASTinEnv (env : EnvCtx LispVal) (action : Eval LispVal) : IO (Except LispException LispVal) := do
  (action.run.run env).run

unsafe def basicEnv : EnvCtx LispVal :=
  Prim.primEnv

unsafe def evalExpr (file? : Bool) (stringInput : String) : IO Unit := do
    runASTinEnv basicEnv ((parseWithoutLib stringInput)
    >>= (fun val => /-IO.println s!"Parse res (type: {val.ty}): {val}" *> -/(if file? then evalBody else eval) val))
    >>= (fun evaled => do
        IO.println $ match evaled with
          | .ok r =>  s!"After eval (type: {r.ty}): {r}"
          | .error e => s!"Exception after eval: {e}")
