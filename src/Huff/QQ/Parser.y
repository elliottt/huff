{
-- vim: ft=haskell
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE PatternSynonyms #-}
module Huff.QQ.Parser where

import Huff.Compile.AST
import Huff.QQ.Lexer (lexer,Lexeme(..),Token(..),Keyword(..))

}

%tokentype { Lexeme Token }

%token
  'domain'  { KW K_domain  $$ }
  'problem' { KW K_problem $$ }

%monad { Parse }
%error { parseError }

%name decls decls

%%

decls :: { [Decl ()] }
  : list(decl) { $1 }

decl :: { Decl () }
  : domain  { DDomain  $1 }
  | problem { DProblem $1 }

domain :: { Domain () }
  : 'domain' { undefined }

problem :: { Problem }
  : 'problem' { undefined }

opt(p)
  : {- empty -} { Nothing }
  | p           { Just $1 }

list(p)
  : {- empty -}  { []         }
  | list_rev1(p) { reverse $1 }

list1(p)
  : list_rev1(p) { reverse $1 }

list_rev1(p)
  : p              { [$1]    }
  | list_rev1(p) p { $2 : $1 }

{

type Parse = Either ParseError

data ParseError = ParseError

parseError :: [Lexeme Token] -> Parse a
parseError _ = undefined

pattern KW k loc <- Lexeme { lexemeToken = TKeyword k, lexemeRange = loc }

parseQQ :: String -> Parse [Decl ()]
parseQQ str = decls (lexer str)

}
