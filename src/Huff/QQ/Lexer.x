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
    SourcePos(..),
    SourceRange(..)
  ) where

import           AlexTools
import           Data.Char (isAscii)
import qualified Data.Text as T

}

$upper  = [A-Z]
$lower  = [a-z]
$number = [0-9]

@ident    = $lower [$upper $lower $number _]*
@conident = $upper [$upper $lower $number _]*

:-

<0> {

-- skip whitespace
$white+ ;

"{"         { keyword K_lbrace    }
"}"         { keyword K_rbrace    }
"("         { keyword K_lparen    }
")"         { keyword K_rparen    }
"="         { keyword K_assign    }
"|"         { keyword K_pipe      }
","         { keyword K_comma     }
":"         { keyword K_colon     }
"!"         { keyword K_not       }
"domain"    { keyword K_domain    }
"predicate" { keyword K_predicate }
"operator"  { keyword K_operator  }
"requires"  { keyword K_requires  }
"effect"    { keyword K_effect    }
"object"    { keyword K_object    }

@ident      { matchText >>= \t -> lexeme (TIdent    t) }
@conident   { matchText >>= \t -> lexeme (TConIdent t) }

.           { lexeme TError }

}


{
-- Lexer -----------------------------------------------------------------------

data Token = TKeyword  !Keyword
           | TIdent    !T.Text
           | TConIdent !T.Text
           | TError
             deriving (Show)

data Keyword = K_domain
             | K_object
             | K_predicate
             | K_operator
             | K_requires
             | K_effect

             | K_lbrace
             | K_rbrace
             | K_lparen
             | K_rparen

             | K_assign
             | K_pipe
             | K_comma
             | K_colon
             | K_not
               deriving (Show)

keyword :: Keyword -> Action () [Lexeme Token]
keyword kw = lexeme (TKeyword kw)

data Error = E_lexical !SourcePos
             deriving (Show)

lexer :: SourcePos -> String -> [Lexeme Token]
lexer start str = $makeLexer simpleLexer input
  where
  input = (initialInput (T.pack str)) { inputPos = start }

alexGetByte = makeAlexGetByte $ \ c ->
  if isAscii c
     then toEnum (fromEnum c)
     else 0x1
}
