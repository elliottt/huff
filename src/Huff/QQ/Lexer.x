-- vim: ft=haskell

{
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Huff.QQ.Lexer (
    lexer,
    Token(..),
    Keyword(..),
    Lexeme(..),
  ) where

import           AlexTools
import           Data.Char (isAscii)
import qualified Data.Text as T

}

:-

<0> {

-- skip whitespace
$white+ ;

"{"      { keyword K_lbrace }
"}"      { keyword K_rbrace }
"("      { keyword K_lparen }
")"      { keyword K_rparen }

"operator" { keyword K_operator }
"domain"   { keyword K_domain   }
"type"     { keyword K_type     }

"problem"  { keyword K_problem  }

.       { lexeme TError }

}


{
-- Lexer -----------------------------------------------------------------------

data Token = TKeyword !Keyword
           | TIdent   !T.Text
           | TError
             deriving (Show)

data Keyword = K_domain
             | K_type
             | K_lbrace
             | K_rbrace
             | K_lparen
             | K_rparen
             | K_operator
             | K_problem
               deriving (Show)

keyword :: Keyword -> Action () [Lexeme Token]
keyword kw = lexeme (TKeyword kw)

data Error = E_lexical !SourcePos
             deriving (Show)

lexer :: String -> [Lexeme Token]
lexer str = $makeLexer simpleLexer (initialInput (T.pack str))

alexGetByte = makeAlexGetByte $ \ c ->
  if isAscii c
     then toEnum (fromEnum c)
     else 0x1
}
