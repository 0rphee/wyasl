import Cli
import Wyasl.Repl

namespace Wyasl.Cli

open Cli
open Cli.Parsed

unsafe def repl : IO Unit := do
  let stdout <- IO.getStdout
  let stdin <- IO.getStdin
  Wyasl.Repl.repl stdout stdin

unsafe def cliHandler (p : Cli.Parsed) : IO UInt32 := do
  -- TODO: verbose
  let verbose := p.hasFlag "verbose"
  match (.[0]?) =<< p.variableArgsAs? (τ := String) with
  | some (filename : String) => IO.FS.readFile filename >>= Eval.evalExpr true
  | none => repl
  pure 0

unsafe def cli : Cli.Cmd := `[Cli|
  wyasl VIA cliHandler; ["0.0.1"]
  "Scheme interpreter"

  FLAGS:
    v, verbose;             "Show parsed output before evaluation"

  ARGS:
    ...filename : String;      "Filename to interpret, if missing, the repl is opened"

  EXTENSIONS:
    Cli.author "0rphee"
]
