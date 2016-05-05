-- vim: ft=haskell

{
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE RecordWildCards #-}

module Huff.QQ.Lexer (
    lexer,
    Source, LToken,
    Token(..), Keyword(..)
  ) where

import           Data.Char (isAscii,isSpace,ord)
import           Data.Maybe (fromMaybe)
import qualified Data.Text.Lazy as L
import           Data.Word (Word8)
import           Text.Location (at,Located,Range(..),Position(..),movePos,thing)

}


:-

<0> {

-- skip whitespace
$white+ ;

"{"      { keyword K_lbrace }
"}"      { keyword K_rbrace }

"$("     { startSplice }

"        { startQuote }

"domain" { keyword K_domain }
"type"   { keyword K_type   }

}

<quote> {

\\"     { addQuote }
[^\\"]+ { addQuote }
"       { endQuote }

}

<splice> {

"("      { nestSplice }
")"      { endSplice  }
[^\)]+   { addSplice  }

}

{


-- Lexer -----------------------------------------------------------------------

type Source = String
type LToken = Located Source Token

data Token = TKeyword !Keyword
           | TIdent   !L.Text
           | TSplice  !L.Text
           | TQuote   !L.Text
           | TError   !L.Text
             deriving (Show)

data Keyword = K_domain
             | K_type
             | K_lbrace
             | K_rbrace
               deriving (Show)

data Error = E_lexical !Position
             deriving (Show)


lexer :: Source -> Maybe Position -> L.Text -> [LToken]
lexer src mbStart inp = go AlexInput { aiPos = startPos, aiText = inp } Normal
  where
  startPos = fromMaybe (Position 1 1) mbStart

  rangeSource = Just src

  go inp st =
    case alexScan inp (modeToInt st) of

      AlexEOF ->
        []

      AlexError inp' ->
        let (as,bs) = L.break isSpace (aiText inp')
            pos'    = L.foldl' (flip move) (aiPos inp') as
            inp2    = AlexInput { aiPos = pos', aiText = bs }
            loc     = Range { rangeStart = aiPos inp', rangeEnd = pos', .. }
        in (TError as `at` loc) : go inp2 st

      AlexSkip inp' _ ->
        go inp' st

      AlexToken inp' len act ->
        case act rangeSource len inp st of
          (st',xs) -> xs ++ go inp' st'



-- Utilities -------------------------------------------------------------------

data AlexInput = AlexInput { aiPos :: !Position, aiText :: !L.Text }

data Mode = Normal
          | Splice !Int !Position !L.Text
          | Quote !Position ![L.Text]
            deriving (Show)

modeToInt :: Mode -> Int
modeToInt Normal   = 0
modeToInt Splice{} = splice
modeToInt Quote{}  = quote

type AlexAction = Maybe Source -> Int -> AlexInput -> Mode -> (Mode,[LToken])

move :: Char -> Position -> Position
move  = movePos 8

withInput :: (L.Text -> Token) -> Maybe Source -> Int -> AlexInput -> LToken
withInput mk rangeSource len AlexInput { .. } =
  mk txt `at` Range { rangeStart = aiPos
                    , rangeEnd   = L.foldl' (flip move) aiPos txt
                    , .. }
  where
  txt = L.take (fromIntegral len) aiText

keyword :: Keyword -> AlexAction
keyword kw src len inp mode = (mode,[withInput (\_ -> TKeyword kw) src len inp])

startSplice :: AlexAction
startSplice _ len inp mode =
  case mode of
    Normal -> (Splice 1 (aiPos inp) L.empty, [])
    _      -> error "Expected to be in Normal"
  where
  txt = L.take (fromIntegral len) (aiText inp)


addSplice :: AlexAction
addSplice _ len inp mode =
  case mode of
    Splice p start acc -> (Splice p start (acc `L.append` txt), [])
    _                  -> error "Expected to be in Splice"
  where
  txt = L.take (fromIntegral len) (aiText inp)

endSplice :: AlexAction
endSplice rangeSource len inp mode =
  case mode of
    Splice p start acc
      | p <= 1    -> (Normal, [ TSplice (acc `L.append` txt) `at` loc start ])
      | otherwise -> (Splice (p-1) start (acc `L.append` txt), [])
    _ -> error "Expected to be in Splice"
  where
  txt            = L.take (fromIntegral (len - 1)) (aiText inp)
  loc rangeStart = Range { rangeEnd = L.foldl (flip move) (aiPos inp) txt, .. }

nestSplice :: AlexAction
nestSplice _ len inp mode =
  case mode of
    Splice p start acc -> (Splice (p + 1) start (acc `L.append` txt), [])
    _                  -> error "Expected to be in Splice"
  where
  txt = L.take (fromIntegral len) (aiText inp)

alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte AlexInput { .. } =
  do (c,rest) <- L.uncons aiText
     return (byteForChar c, AlexInput { aiText = rest, aiPos = move c aiPos, .. })

byteForChar :: Char -> Word8
byteForChar c
  | isAscii c = fromIntegral (ord c)
  | otherwise = 0


-- States ----------------------------------------------------------------------

startQuote :: AlexAction
startQuote _ _ inp _ = (Quote (aiPos inp) [], [])

addQuote :: AlexAction
addQuote _ len inp mode =
  case mode of
    Quote start strs ->
      let str = L.take (fromIntegral len) (aiText inp)
       in (Quote start (str:strs), [])

    _ -> error "Expected to be in Quote"

endQuote :: AlexAction
endQuote _ len inp (Quote start xs) = (Normal, [tok])
  where
  tok = TQuote (L.concat (reverse xs)) `at` Range { rangeStart = start
                                                  , rangeEnd   = end }

  txt = L.take (fromIntegral len) (aiText inp)
  end = L.foldl' (flip move) (aiPos inp) txt

}
