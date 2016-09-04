{
-- vim: ft=haskell
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
module Huff.QQ.Parser where

import Huff.Compile.AST
import Huff.QQ.Lexer (lexer,Lexeme(..),Token(..),Keyword(..),SourcePos,sourceFrom)

}

%tokentype { Lexeme Token }

%token
  IDENT       { $$ @ Lexeme { lexemeToken = TIdent    {} } }
  CONIDENT    { $$ @ Lexeme { lexemeToken = TConIdent {} } }

  'domain'    { KW K_domain    $$ }
  'type'      { KW K_type      $$ }
  'predicate' { KW K_predicate $$ }
  'problem'   { KW K_problem   $$ }
  '{'         { KW K_lbrace    $$ }
  '}'         { KW K_rbrace    $$ }
  '='         { KW K_assign    $$ }
  '|'         { KW K_pipe      $$ }

%monad { Parse }
%error { parseError }

%name decls decls

%%

-- Declarations ----------------------------------------------------------------

decls :: { [Decl ()] }
  : list(decl) { $1 }

decl :: { Decl () }
  : domain  { DDomain  $1 }
  | problem { DProblem $1 }


-- Domains ---------------------------------------------------------------------

domain :: { Domain () }
  : 'domain' CONIDENT '{' list(domain_elem) '}'
    { foldl (flip id) (Domain (lexemeText $2) [] [] []) $4 }

domain_elem :: { Domain () -> Domain () }
  : type_decl { $1 }

type_decl :: { Domain () -> Domain () }
  : 'type' CONIDENT '=' sep1(CONIDENT, '|')
    { let { ty   = lexemeText $2
          ; objs = [ Typed lexemeText ty | Lexeme { .. } <- $4 ] }
       in \dom -> dom { domObjects = domObjects dom } }


-- Problems --------------------------------------------------------------------

problem :: { Problem }
  : 'problem' { undefined }


-- Utilities -------------------------------------------------------------------

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

sep1(p,q)
  : sep_rev(p,q) { reverse $1 }

sep_rev(p,q)
  : p                { [$1]    }
  | sep_rev(p,q) q p { $3 : $1 }

{

type Parse = Either ParseError

data ParseError = ParseError !SourcePos
                  deriving (Show)

parseError :: [Lexeme Token] -> Parse a
parseError (tok:_) = Left (ParseError (sourceFrom (lexemeRange tok)))

pattern KW k loc <- Lexeme { lexemeToken = TKeyword k, lexemeRange = loc }

parseQQ :: SourcePos -> String -> Parse [Decl ()]
parseQQ start str = decls (lexer start str)

}
