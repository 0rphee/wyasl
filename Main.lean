import Wyasl

def main : IO Unit := do
  IO.println s!"Hello, World!"
  IO.println s!"Wyasl: {repr Wyasl.Parser.commentStart}"
