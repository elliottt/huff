module Huff.QQ ( huff ) where

import Huff.QQ.Lexer (SourcePos(..))
import Huff.QQ.Parser (parseQQ)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote (QuasiQuoter(..))


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
       Right ds -> fail (show ds)
