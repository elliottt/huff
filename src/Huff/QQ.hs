{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Huff.QQ ( huff ) where

import           Huff.Compile as AST hiding (Name)
import qualified Huff.Input as Input
import           Huff.QQ.Lexer (SourcePos(..))
import           Huff.QQ.Parser (parseQQ)

import           Control.Monad (forM)
import           Data.Char (toLower)
import           Data.Function (on)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
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
     runIO (print loc)
     let (line,col) = loc_start loc
     let start = SourcePos { sourceIndex  = 0
                           , sourceLine   = line
                           , sourceColumn = col }
     case parseQQ start str of
       Left err -> fail ("huff: " ++ show err)
       Right ds ->
         do dss <- mapM genDomain ds
            return (concat dss)

-- | Translate the domain into one data declaration per `type`, as well as one
-- big data declaration for the domain, with one constructor per operator.
-- Additionally, write out an altered version of the domain, that will produce
-- values of the new domain type.
genDomain :: Domain T.Text -> Q [Dec]
genDomain d@Domain { .. } =
  do let types = mkTypeMap domObjects
     objs     <- mapM genObjectDecl (Map.toList types)
     dom      <- genDomainDecl domName domOperators
     predss   <- mapM genPredicate domPreds
     domValue <- genDomainValue d
     return (dom : domValue ++ objs ++ concat predss)

mkTypeMap :: [Object] -> Map.Map T.Text [T.Text]
mkTypeMap  = foldl step Map.empty
  where
  step acc Typed { .. } = Map.alter (update tValue) tType acc
  update val Nothing    = Just [val]
  update val (Just vs)  = Just (val:vs)

-- | Generate a data declaration from an object definition.
--
-- INVARIANT: all objects are assumed to have the same type.
genObjectDecl :: (T.Text,[T.Text]) -> Q Dec
genObjectDecl (ty,objs) =
  do show <- [t| Show |]
     let cons = [ NormalC (mkName (T.unpack obj)) [] | obj <- objs ]
     return (DataD [] (mkName (T.unpack ty)) [] Nothing cons [show])

-- | Generate a specialized predicate that can produce either a literal, or a
-- term. Produces one type-class per predicate, with instances for literals and
-- terms.
genPredicate :: AST.Pred -> Q [Dec]
genPredicate (App f xs) =
  do let clsName = mkName ("Has_" ++ T.unpack f)
         var     = mkName "a"
         pred    = mkName (T.unpack f)
         arrow x = AppT (AppT ArrowT x)

         params  = take (length xs) [ mkName ("x" ++ show x) | x <- [ 1 .. ] ]

     instLiteral <- [t| $(conT clsName) Literal |]
     instTerm    <- [t| $(conT clsName) Term    |]

     let mkArg p = [| AName (T.pack (show $(varE p))) |]
     litBody <- [| LAtom (App $(text f) $(listE (map mkArg params))) |]

     termBody <- [| TLit $(foldl appE (varE pred) (map varE params)) |]

     return [ ClassD [] clsName [PlainTV var] []
              [ SigD pred (foldr arrow (VarT var) [ ConT (mkName (T.unpack x)) | x <- xs ])
              ]

            , InstanceD Nothing [] instLiteral
              [ FunD pred [ Clause (map VarP params) (NormalB litBody) [] ]
              ]

            , InstanceD Nothing [] instTerm
              [ FunD pred [ Clause (map VarP params) (NormalB termBody) [] ]
              ]
            ]

genDomainDecl :: T.Text -> [Operator T.Text] -> Q Dec
genDomainDecl dom ops =
  do show <- [t| Show |]
     let tyName = mkName (T.unpack dom)
     cons <- mapM mkOpCon ops
     return (DataD [] tyName [] Nothing cons [show])


mkOpCon :: Operator T.Text -> Q Con
mkOpCon op =
  do let conName = mkName (T.unpack (opName op))
     fields <- forM (opParams op) $ \ Typed { .. } ->
       do let tyName = mkName (T.unpack tType)
          bangType (bang noSourceUnpackedness noSourceStrictness) (conT tyName)

     return (NormalC conName fields)


genDomainValue :: Domain T.Text -> Q [Dec]
genDomainValue Domain { .. } =
  do let n          = mkDomVar (T.unpack domName)
         typesC     = typeMap domObjects

         mkCon args name =
           let con x = ConE (mkName (T.unpack x))
            in foldl AppE (con name) (map con args)

         opsC = compileOperators mkCon typesC domOperators

     body <-
       [d| $(varP n) =
             let types = $(liftTypes typesC)
                 ops   = $(listE (map liftOperator opsC))
              in \ start goal -> compileProblem types ops (Problem start goal)
         |]

     let domType = mkName (T.unpack domName)
     sigType <- [t| [AST.Literal] -> AST.Term -> Input.Spec $(conT domType) |]
     let sig = SigD n sigType

     return (sig:body)

liftTypes :: TypeMap T.Text -> Q Exp
liftTypes (TypeMap ts) = [| TypeMap (Map.fromList $(listE (map mkPair (Map.toList ts)))) |]
  where
  mkPair (k,xs) = [| ($(text k), $(listE (map text xs))) |]

text :: T.Text -> Q Exp
text str = [| T.pack $(lift (T.unpack str)) |]

-- | Lift a grounded operator.
liftOperator :: Operator Exp -> Q Exp
liftOperator Operator { .. } =
  [| Operator { opName    = $(text opName)
              , opDerived = $(lift opDerived)
              , opParams  = []
              , opVal     = $(liftVal opVal)
              , opPrecond = $(liftTerm opPrecond)
              , opEffects = $(liftEffect opEffects)
              } |]
  where
  liftVal :: Maybe Exp -> Q Exp
  liftVal Nothing  = [| Nothing          |]
  liftVal (Just e) = [| Just $(return e) |]

-- | Lift a precondition from a grounded operator.
liftTerm :: Term -> Q Exp
liftTerm (TAnd ts)  = [| TAnd $(listE (map liftTerm ts))  |]
liftTerm (TOr  ts)  = [| TOr  $(listE (map liftTerm ts))  |]
liftTerm (TLit lit) = [| TLit $(liftLit lit)              |]
liftTerm t          = fail ("Compilation pass missed something: " ++ show t)

liftLit :: Literal -> Q Exp
liftLit (LAtom a) = [| LAtom $(liftAtom a) |]
liftLit (LNot  a) = [| LNot  $(liftAtom a) |]

liftAtom :: Atom -> Q Exp
liftAtom (App f xs) = [| App $(text f) $(listE (map liftArg xs)) |]

liftArg :: Arg -> Q Exp
liftArg (AName n) = [| AName $(text n) |]
liftArg (AVar  n) = [| AVar  $(text n) |]

-- | Lift effects from a grounded operator.
liftEffect :: Effect -> Q Exp
liftEffect (EWhen p qs) = [| EWhen $(liftTerm p) $(listE (map liftLit qs)) |]
liftEffect (EAnd es)    = [| EAnd  $(listE (map liftEffect es))            |]
liftEffect (ELit lit)   = [| ELit  $(liftLit lit)                          |]
liftEffect e            = fail ("Compilation pass missed something: " ++ show e)

mkDomVar :: String -> Name
mkDomVar (h:tl) = mkName (toLower h : tl)
mkDomVar []     = error "Invalid domain name: no name given"
