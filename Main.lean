import Wyasl.Cli

unsafe def main (args : List String): IO UInt32 := do
  Wyasl.Cli.cli.validate args
