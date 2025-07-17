import Wyasl.LispVal
import Wyasl.Eval

namespace Wyasl.Repl

open Wyasl.LispVal

unsafe def process (str : String) : IO Unit :=
  Eval.evalExpr false str

unsafe def repl (stdout : IO.FS.Stream) (stdin : IO.FS.Stream) : IO Unit := do
  stdout.putStr "Repl> " *> stdout.flush
  let line <- stdin.getLine
  if line.isEmpty
  then stdout.putStr "\n"
  else process line *> repl stdout stdin
