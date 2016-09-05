{-# LANGUAGE RecordWildCards #-}

module Huff.QQ ( huff ) where

import Huff.Compile.AST
import Huff.QQ.Lexer (SourcePos(..))
import Huff.QQ.Parser (parseQQ)

import           Data.Function (on)
import           Data.List (groupBy,sortBy)
import qualified Data.Text as T
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import           Language.Haskell.TH.Quote (QuasiQuoter(..))


huff :: QuasiQuoter
huff  = QuasiQuoter { quoteExp  = notSupported "expressions"
                    , quotePat  = notSupported "patterns"
                    , quoteType = notSupported "types"
                    , quoteDec  = huffDecs
                    }
  where
  notSupported n _ = fail ("huff: Quasi-quotation is not supported for " ++ n)

huffDecs :: String -> Q [Dec]
huffDecs str =
  do loc <- location
     qRunIO (print loc)
     let (line,col) = loc_start loc
     let start = SourcePos { sourceIndex  = 0
                           , sourceLine   = line
                           , sourceColumn = col }
     case parseQQ start str of
       Left err -> fail ("huff: " ++ show err)
       Right ds ->
         do dss <- mapM genDecl ds
            return (concat dss)

genDecl :: Decl () -> Q [Dec]
genDecl (DDomain dom) = genDomain dom
genDecl (DProblem p)  = fail "genDecl: problem"


-- | Translate the domain into one data declaration per `type`, as well as one
-- big data declaration for the domain, with one constructor per operator.
-- Additionally, write out an altered version of the domain, that will produce
-- values of the new domain type.
genDomain :: Domain () -> Q [Dec]
genDomain Domain { .. } =
  do mapM genObject (groupObjects domObjects)


-- | Group objects together that have the same type.
groupObjects :: [Object] -> [[Object]]
groupObjects  = groupBy ((==) `on` tType) . sortBy (compare `on` tType)

-- | Generate a data declaration from an object definition.
--
-- INVARIANT: all objects are assumed to have the same type.
genObject :: [Object] -> Q Dec
genObject objs =
  do let objType = tType (head objs)
     let cons = [ NormalC (mkName (T.unpack (tValue obj))) [] | obj <- objs ]
     return (DataD [] (mkName (T.unpack objType)) [] Nothing cons [])
