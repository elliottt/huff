{
-- vim: ft=haskell
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
module Huff.QQ.Parser where

import Huff.Compile.AST
import Huff.QQ.Lexer (lexer,Lexeme(..),Token(..),Keyword(..),SourcePos,sourceFrom)

import qualified Data.Text as T

}

%tokentype { Lexeme Token }

%token
  IDENT       { $$ @ Lexeme { lexemeToken = TIdent    {} } }
  CONIDENT    { $$ @ Lexeme { lexemeToken = TConIdent {} } }

  'domain'    { KW K_domain    $$ }
  'object'    { KW K_object    $$ }
  'predicate' { KW K_predicate $$ }
  'operator'  { KW K_operator  $$ }
  'requires'  { KW K_requires  $$ }
  'effect'    { KW K_effect    $$ }
  '{'         { KW K_lbrace    $$ }
  '}'         { KW K_rbrace    $$ }
  '('         { KW K_lparen    $$ }
  ')'         { KW K_rparen    $$ }
  ','         { KW K_comma     $$ }
  '='         { KW K_assign    $$ }
  '|'         { KW K_pipe      $$ }
  ':'         { KW K_colon     $$ }
  '!'         { KW K_not       $$ }

%monad { Parse }
%error { parseError }

%name domains domains

%%

-- Domains ---------------------------------------------------------------------

domains :: { [Domain T.Text] }
  : list1(domain) { $1 }

domain :: { Domain T.Text }
  : 'domain' CONIDENT '{' list(domain_elem) '}'
    { foldr id (Domain (lexemeText $2) [] [] []) $4 }

domain_elem :: { Domain T.Text -> Domain T.Text }
  : object_decl    { $1 }
  | predicate_decl { $1 }
  | operator_decl  { $1 }

object_decl :: { Domain T.Text -> Domain T.Text }
  : 'object' type '=' sep1(CONIDENT, '|')
    { let { objs = [ Typed lexemeText $2 | Lexeme { .. } <- $4 ] }
       in \dom -> dom { domObjects = objs ++ domObjects dom } }

type :: { Type }
  : CONIDENT { lexemeText $1 }

predicate_decl :: { Domain T.Text -> Domain T.Text }
  : 'predicate' sep1(predicate_spec, ',')
    { foldr (.) id $2 } 

predicate_spec :: { Domain T.Text -> Domain T.Text }
  : IDENT '(' sep1(type, ',') ')'
    { \dom -> dom { domPreds = App (lexemeText $1) $3 : domPreds dom } }

operator_decl :: { Domain T.Text -> Domain T.Text }
  : 'operator' CONIDENT '(' sep(param, ',') ')' '{'
       'requires' ':' sep1(term,   ',')
       'effect'   ':' sep1(effect, ',')
    '}'
    { let { op = Operator { opName = lexemeText $2
                          , opDerived = False
                          , opParams = $4
                          , opVal = Just (lexemeText $2)
                          , opPrecond = TAnd $9
                          , opEffects = EAnd $12
                          } }
       in \dom -> dom { domOperators = op : domOperators dom } }

param :: { Param }
  : IDENT ':' type { Typed (lexemeText $1) $3 }


-- Expressions -----------------------------------------------------------------

term :: { Term }
  : atom     { TLit (LAtom $1) }
  | '!' term { TNot $2 }

effect :: { Effect }
  : literal { ELit $1 }

literal :: { Literal }
  :     atom { LAtom $1 }
  | '!' atom { LNot  $2 }

atom :: { Atom }
  : IDENT '(' sep1(arg, ',') ')'
    { App (lexemeText $1) $3 }

arg :: { Arg }
  : IDENT    { AVar  (lexemeText $1) }
  | CONIDENT { AName (lexemeText $1) }


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

sep(p,q)
  : {- empty -}  { []         }
  | sep_rev(p,q) { reverse $1 }

sep1(p,q)
  : sep_rev(p,q) { reverse $1 }

sep_rev(p,q)
  : p                { [$1]    }
  | sep_rev(p,q) q p { $3 : $1 }

{

type Parse = Either ParseError

data ParseError = ParseError (Maybe SourcePos)
                  deriving (Show)

parseError :: [Lexeme Token] -> Parse a
parseError (tok:_) = Left (ParseError (Just (sourceFrom (lexemeRange tok))))
parseError []      = Left (ParseError Nothing)

pattern KW k loc <- Lexeme { lexemeToken = TKeyword k, lexemeRange = loc }

parseQQ :: SourcePos -> String -> Parse [Domain T.Text]
parseQQ start str = domains toks
  where
  toks = lexer start str

}
