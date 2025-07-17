import Parser
import Wyasl.LispVal

namespace Wyasl.Parser
open Wyasl.LispVal

abbrev WParser a := SimpleParserT Substring Char IO a

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
  let _ <- Parser.withBacktracking <| Parser.Char.string commentLine
  WParser.skipMany (Parser.tokenFilter (. != '\n'))

mutual
partial def WParser.inCommentMulti : WParser Unit :=
  ((Parser.withBacktracking <| Parser.Char.string commentEnd) *> pure ())
  <|> (multiLineComment                            *> inCommentMulti)
  <|> (WParser.skipMany1 (WParser.noneOf startEnd) *> inCommentMulti )
  <|> (WParser.noneOf startEnd                     *> inCommentMulti )
partial def WParser.multiLineComment := do
  let _ <- Parser.withBacktracking <| Parser.Char.string commentStart
  inCommentMulti
end

def WParser.whiteSpace : WParser Unit := do
  -- IO.println "whiteSpace"
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

def WParser.quoted (p : WParser a) : WParser a := Parser.withBacktracking (Parser.Char.char '\'' *> p)

def WParser.ident := do
  let c <- identStart
  let cs <- Parser.takeMany identLetter
  pure <| String.mk <| c :: cs.toList

def WParser.tokIdentifier := lexeme WParser.ident

def WParser.specialIdentifier :=
  lexeme <| Parser.withBacktracking do
    Parser.Char.string "-"
    <|> Parser.Char.string "+"
    <|> Parser.Char.string "..."

def WParser.identifier : WParser String :=
  WParser.tokIdentifier <|> WParser.specialIdentifier

def Radix base := Prod Int64 (WParser base)

-- def numberWithRadix (r : Radix base) : WParser Int64 := do
--   let (base, baseDigit) := r
--   let digits <- Parser.takeMany1 baseDigit
--   let n := digits.foldl (fun x d => base * x + )
--   sorry

-- contrary to the decimal impl in parsec, this already takes into account the sign
def WParser.decimal : WParser Int64 :=
  Int.toInt64 <$> Parser.Char.ASCII.parseInt (decimalOnly := true)

-- not needed ?
-- sign :: Parser (Integer -> Integer)
-- numberWithRadix
-- intRadix

def WParser.stringLetter : WParser Char :=
  Parser.tokenFilter (fun c => c != '"' && c != '\\' && c > '\x1A')
  --  haskell: \026 -> \SUB -> U+001A

def WParser.escapeEmpty : WParser Char :=
  Parser.Char.char '&'

def WParser.escapeGap : WParser Char :=
  Parser.dropMany1 Parser.Char.space *> Parser.Char.char '\\'

def WParser.charNum : WParser Char := do
  let code <- Parser.Char.ASCII.parseNat (decimalOnly := false)
  if code > 0x10FFFF
  then Parser.throwUnexpectedWithMessage (msg := "Invalid escape sequence")
  else pure <| Char.ofNat code

def escMap : Array (Prod Char Char) :=
  #[('a','\x07'), ( 'b', '\x08'), ( 'f','\x0C'), ( 'n','\n'), ( 'r','\r'), ( 't','\t'), ( 'v','\x0B'), ('\\', '\\'), ('"', '"'), ('\'','\'')]

def WParser.charEsc : WParser Char :=
  escMap.foldl (fun ac next => ac <|> (parseEsc next)) (Parser.throwUnexpectedWithMessage (msg := "choice comb"))
  where
    parseEsc (pair : Prod Char Char) : WParser Char := do
      Parser.Char.char pair.fst *> pure pair.snd

def asciiMap : Array (Prod String Char) :=
 #[("NUL", '\x00'), ("SOH", '\x01'), ("STX", '\x02'), ("ETX", '\x03'), ("EOT", '\x04'), ("ENQ", '\x05'), ("ACK", '\x06'), ("BEL", '\x07'), ("DLE", '\x10'), ("DC1", '\x11'), ("DC2", '\x12'), ("DC3", '\x13'), ("DC4", '\x14'), ("NAK", '\x15'), ("SYN", '\x16'), ("ETB", '\x17'), ("CAN", '\x18'), ("SUB", '\x1A'), ("ESC", '\x1B'), ("DEL", '\x7F'), ("BS", '\x08' ) ,("HT", '\x09') ,("LF", '\x0A') ,("VT", '\x0B') ,("FF", '\x0C') ,("CR", '\x0D') ,("SO", '\x0E') ,("SI", '\x0F') ,("EM", '\x19') ,("FS", '\x1C') ,("GS", '\x1D') ,("RS", '\x1E') ,("US", '\x1F') ,("SP", ' ')]

def WParser.charAscii : WParser Char :=
  asciiMap.foldl (fun ac next => ac <|> (parseAscii next)) (Parser.throwUnexpectedWithMessage (msg := "choice comb"))
  where
    parseAscii (pair : Prod String Char) : WParser Char :=
      Parser.withBacktracking
        (Parser.Char.string pair.fst *> pure pair.snd)

def WParser.charControl : WParser Char := do
  let _ <- Parser.Char.char '^'
  let code <- Parser.Char.Unicode.uppercase
  pure <| Char.ofNat (code.toNat - 'A'.toNat + 1)

def WParser.escapeCode : WParser Char :=
  charEsc <|> charNum <|> charAscii <|> charControl

def WParser.stringEscape : WParser (Option Char) := do
  let _ <- Parser.Char.char '\\'
  (escapeGap *> pure none)
    <|> (escapeEmpty *> pure none)
    <|> (some <$> escapeCode)

def WParser.stringChar : WParser (Option Char) :=
  (some <$> stringLetter)
  <|> stringEscape


def WParser.stringLiteral : WParser String :=
  lexeme do
    let str <- between
                delimiter
                delimiter
                (Parser.takeMany stringChar)
    pure
      <| String.mk
      <| str.foldr
          (fun x acc => match x with | some c => c :: acc | none => acc)
          []
  where
    delimiter := (Parser.Char.char '"')

def WParser.textLiteral : WParser String := WParser.stringLiteral

def WParser.nil : WParser Unit :=
  Parser.withBacktracking (Parser.Char.char '\'' *> Parser.Char.string "()") *> pure ()

unsafe def WParser.hashVal : WParser LispVal := do
  -- println! "hashVal"
  let a <- lexeme do
    let _ <- Parser.Char.char '#'
    -- println! "after #"
    (   (Parser.Char.char 't' *> pure (LispVal.bool true))
    <|> (Parser.Char.char 'f' *> pure (LispVal.bool false))
    <|> (Parser.Char.char 'b' *> (fromNat <$> Parser.Char.ASCII.parseNat.binNum))
    <|> (Parser.Char.char 'o' *> (fromNat <$> Parser.Char.ASCII.parseNat.octNum ))
    <|> (Parser.Char.char 'd' *> (fromNat <$> Parser.Char.ASCII.parseNat (decimalOnly := true)) )
    <|> (Parser.Char.char 'x' *> (fromNat <$> Parser.Char.ASCII.parseNat.hexNum))
    <|> (oneOf #['e','i'] *> Parser.throwUnexpectedWithMessage (msg := "Unsupported: exactness"))
    <|> (Parser.Char.char '(' *> Parser.throwUnexpectedWithMessage (msg := "Unsupported: vector"))
    <|> (Parser.Char.char '\\' *> Parser.throwUnexpectedWithMessage (msg := "Unsupported: char"))
    )
  -- println! "after hashVal {a}"
  pure a
  where
    fromNat := LispVal.number ∘ Nat.toInt64

unsafe def WParser.quote (v : LispVal) : LispVal :=
  .list [.atom "quote", v]

mutual
unsafe def WParser.manyLispVal : WParser (List LispVal) :=
  Array.toList <$> Parser.sepBy whiteSpace lispVal

unsafe def WParser.lispVal : WParser LispVal := do
  -- println! "before lispVal"
  let r <- (hashVal
    <|> (nil *> pure .nil)
    <|> (.number <$> (Parser.withBacktracking decimal))
    <|> (.atom <$> identifier)
    <|> (.string <$> textLiteral)
    <|> (quote <$> quoted lispVal)
    <|> (.list <$> parens manyLispVal)
    )
  -- println! "after lispVal"
  pure r
end

def WParser.contents [ToString a] (p : WParser a) : WParser a := do
  -- println! "start contents"
  whiteSpace
  let r <- lexeme p
  -- println! "after lexeme p: {r}"
  Parser.endOfInput
  pure r

unsafe def WParser.readExpr (input : String ) : IO (Parser.Result (Parser.Error.Simple Substring Char)  Substring LispVal) :=
  ParserT.run (contents lispVal) input.toSubstring

unsafe def WParser.readExprFile (input : String ) : IO (Parser.Result (Parser.Error.Simple Substring Char) Substring LispVal) :=
  ParserT.run (contents (.list <$> manyLispVal)) input.toSubstring

unsafe def WParser.showRes (input : String) : IO String := do
  pure <| match <- WParser.readExpr input with
  | .ok rest v => "Rest: " ++ rest.toString ++ "\nResult: " ++ (v.toString)
  | .error rest e => "Rest: " ++ rest.toString ++ "\nError: " ++ (toString e)
