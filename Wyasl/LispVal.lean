import Std.Data.TreeMap

-- set_option diagnostics true

namespace Wyasl.LispVal

abbrev EnvCtx a := Std.TreeMap String a

def EvalT c e m a := ReaderT (EnvCtx c) (ExceptT e m) a
abbrev Ev env err a := EvalT env err IO a

namespace EvalT

def mk (x : ReaderT (EnvCtx c) (ExceptT e m) a) : EvalT c e m a := x
def run (x : EvalT c e m a) : ReaderT (EnvCtx c) (ExceptT e m) a := x
def lift [Monad m] (x : m a) : EvalT c e m a :=
  MonadLift.monadLift
    (m := ExceptT e m)
    (n := ReaderT (EnvCtx c) (ExceptT e m))
    (ExceptT.lift x)
def mkE (x : ExceptT e m a) : EvalT c e m a :=
  MonadLift.monadLift
    (m := ExceptT e m)
    (n := ReaderT (EnvCtx c) (ExceptT e m))
    x
def pure [Monad m] (x : a) : EvalT c e m a := mk <| ReaderT.pure x
def bind {e a b : Type} {m : Type -> Type} [Monad m] (x : EvalT c e m a) (f : a -> EvalT c e m b) : EvalT c e m b :=
  mk <| ReaderT.bind x.run  (run ∘ f)
def read [Monad m] : EvalT c e m (EnvCtx c) := mk ReaderT.read
def withReader [Monad m] (f : EnvCtx c -> EnvCtx c) (act : EvalT c e m a) : EvalT c e m a :=
  mk <| MonadWithReader.withReader f act.run

instance [Monad m] : Monad (EvalT c e m) where
  pure := EvalT.pure
  bind := EvalT.bind

instance [Monad m] : MonadLift m (EvalT c e m) where
  monadLift x := EvalT.lift x

instance instApplicativeOfMonad [Monad m] : Applicative (EvalT c e m) where
  pure := EvalT.pure
  seq f x r := Seq.seq (f r ) fun _ => x () r
  seqLeft  a b r := SeqLeft.seqLeft (a r) fun _ => b () r
  seqRight a b r := SeqRight.seqRight (a r) fun _ => b () r

instance instMonadExceptEvalT [Monad m] : MonadExcept e (EvalT c e m) where
  throw {α} er := EvalT.mkE (throw er : ExceptT e m α )
  tryCatch action handler :=
    EvalT.mk (tryCatch action.run (EvalT.run ∘ handler))

instance [Monad m] : MonadReader (EnvCtx c) (EvalT c e m) where
  read := EvalT.read

instance [Monad m] : MonadWithReader (EnvCtx c) (EvalT c e m) where
  withReader f act := EvalT.withReader f act
end EvalT

abbrev FuncT res err := List res -> Ev res err res

mutual
unsafe inductive LispException where
  | numArgs        : Int64 -> List LispVal -> LispException
  | lengthOfList   : String -> Int -> LispException
  | expectedList   : String  -> LispException
  | typeMismatch   : String -> LispVal -> LispException
  | badSpecialForm : String -> LispException
  | notFunction    : LispVal -> LispException
  | unboundVar     : String -> LispException
  | default        : LispVal -> LispException
  | pError         : String -> LispException
  | ioError        : String -> LispException

unsafe inductive LispVal where
  | atom   : String -> LispVal
  | list   : List LispVal -> LispVal
  | number : Int64 -> LispVal
  | string : String -> LispVal
  | fn     : FuncT LispVal LispException -> LispVal
  | lambda : FuncT LispVal LispException -> EnvCtx LispVal -> LispVal
  | nil    : LispVal
  | bool   : Bool -> LispVal
end

unsafe def unwords (formatter : LispVal -> Std.Format) (l : List LispVal) :  Std.Format := ((l.map formatter).intersperse (.text " ")).foldl (. ++ .) ""

unsafe def showVal : LispVal -> Std.Format
  | .atom a => .text a
  | .list a => "(" ++ unwords showVal a ++ ")"
  | .number a => repr a
  | .string a => repr a
  | .fn _ => "(internal function)"
  | .lambda _ _ => "(lambda function)"
  | .nil => "Nil"
  | .bool false => "#f"
  | .bool true => "#t"

unsafe def LispVal.ty : LispVal -> String
  | .atom _ => "atom"
  | .list _ => "list"
  | .number _ => "number "
  | .string _ => "string "
  | .fn _ => "function"
  | .lambda _ _ => "lambda"
  | .nil => "nil"
  | .bool _ => "bool"

unsafe instance : Repr LispVal where
  reprPrec v _ := showVal v

unsafe instance : ToString LispVal where
  toString v := Std.Format.pretty <| showVal v

unsafe def LispVal.toString (v : LispVal) : String
  := ToString.toString v

unsafe def LispException.fmt : LispException -> Std.Format
  | .numArgs n args       =>  s!"Error Number Arguments, expected {toString n} received args: {unwords showVal args}"
  | .lengthOfList msg n   => s!"Error Length of List in {msg} length: {toString n}"
  | .expectedList msg     => s!"Error Expected List in function {msg}"
  | .typeMismatch msg val => s!"Error Type Mismatch: {msg} {showVal val}"
  | .badSpecialForm msg   => s!"Error Bad Special Form: {msg}"
  | .notFunction val      => s!"Error Not a Function: {showVal val}"
  | .unboundVar name      => s!"Error Unbound Variable: {name}"
  | .default val          => s!"Error, Danger Will Robinson! Evaluation could not proceed! {showVal val} "
  | .pError parserError   => s!"Parser Error, expression cannot evaluate: {parserError}"
  | .ioError msg          => s!"Error reading file: {msg}"


unsafe instance : ToString LispException where
  toString v := Std.Format.pretty $ v.fmt

unsafe abbrev Eval := Ev LispVal LispException
unsafe abbrev Func := FuncT LispVal LispException

export LispVal.LispVal (atom list number string fn lambda nil bool)
