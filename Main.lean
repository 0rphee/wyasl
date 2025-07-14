import Wyasl
import Wyasl.Parser

open Wyasl.Parser

unsafe def main : IO Unit := do
  IO.println "main"
  
  IO.println s!"{<- WParser.showRes "#t"}"
