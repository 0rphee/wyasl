import Parser
import Wyasl.LispVal

namespace Wyasl.Parser
open Wyasl.LispVal

abbrev WParser a := Parser Unit Substring Char a

-- lexer :: Tok.GenTokenParser T.Text () Identity
-- lexer = Tok.makeTokenParser style-- style :: Tok.GenLanguageDef T.Text () Identity
-- style = Lang.emptyDef {
--   Tok.commentStart = "{-"
--   , Tok.commentEnd = "-}"
--   , Tok.commentLine = ";"
--   , Tok.opStart = mzero
--   , Tok.opLetter = mzero
--   , Tok.identStart = letter <|> oneOf "!$%&*/:<=>?^_~"
--   , Tok.identLetter = digit <|> letter <|> oneOf "!$%&*/:<=>?^_~+-.@"
--   }
-- 
-- otherwise = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")

def commentStart := "{-"
def commentEnd := "-}"
def commentLine := ";"
def nestedComments := true

def startEnd := (commentEnd ++ commentStart).toList.eraseDups.toArray

-- zero or more times
def WParser.skipMany (p : WParser a) : WParser Unit := Parser.dropMany p
-- 
-- one or more times
def WParser.skipMany1 (p : WParser a) : WParser Unit := Parser.dropMany1 p

def WParser.noneOf (cs : Array Char) : WParser Char := Parser.tokenFilter (fun c => !cs.elem c)
def WParser.oneOf (cs : Array Char) : WParser Char := Parser.tokenFilter (fun c => cs.elem c)

def identStart :=
  Parser.Char.Unicode.alpha
  <|> WParser.oneOf
        #['!', '$', '%', '&', '*', '/', ':', '<', '=', '>', '?', '^', '_', '~', ]
def identLetter :=
  Parser.Char.ASCII.alphanum
  <|> WParser.oneOf
        #['!', '$', '%', '&', '*', '/', ':', '<', '=', '>', '?', '^', '_', '~', '+', '-', '.', '@', ]

def WParser.simpleSpace : WParser Unit := Parser.Char.Unicode.whitespace *> pure ()
def WParser.oneLineComment := do
  let _ <- Parser.Char.string commentLine 
  WParser.skipMany (Parser.Char.char '\n')

mutual
partial def WParser.inCommentMulti : WParser Unit :=
  (Parser.Char.string commentEnd *> pure ())
  <|> (multiLineComment                            *> inCommentMulti)
  <|> (WParser.skipMany1 (WParser.noneOf startEnd) *> inCommentMulti )
  <|> (WParser.noneOf startEnd                     *> inCommentMulti )
partial def WParser.multiLineComment := do
  let _ <- Parser.Char.string commentStart
  inCommentMulti
end

def WParser.whiteSpace : WParser Unit :=
  WParser.skipMany (WParser.simpleSpace <|> oneLineComment <|> multiLineComment)

def WParser.lexeme (p : WParser out) : WParser out :=
  p <* WParser.whiteSpace
 
def WParser.between
  {err stream : Type} {m : Type -> Type}
  [Parser.Stream stream Char] [Parser.Error err stream Char] [Monad m]
  (popen : ParserT err stream Char m o1)
  (pclose : ParserT err stream Char m o2)
  (p : ParserT err stream Char m out)
  : ParserT err stream Char m out := do 
    popen *> p <* pclose

def WParser.symbolC (c : Char) : WParser Char := lexeme (Parser.Char.char c)
def WParser.symbolS (s : String) : WParser String := lexeme (Parser.Char.string s)

def WParser.parens (p : WParser a) : WParser a :=
  WParser.between (WParser.symbolC '(') (WParser.symbolC ')') p

def WParser.quoted (p : WParser a) : WParser a := Parser.Char.char '\'' *> p

def WParser.ident := do
  let c <- identStart
  let cs <- Parser.takeMany identLetter
  pure <| String.mk <| c :: cs.toList

def WParser.tokIdentifier := lexeme WParser.ident

def WParser.specialIdentifier :=
  lexeme do
    Parser.Char.string "-"
    <|> Parser.Char.string "+"
    <|> Parser.Char.string "..."

def WParser.identifier : WParser String :=
  WParser.tokIdentifier <|> WParser.specialIdentifier

