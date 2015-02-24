{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Huff.Compile.Operators (
  expandActions,
  removeQuantifiers,
  removeDisjunction,
  removeNegation
  ) where

import           Huff.Compile.AST

import           Control.Monad (msum)
import           Data.Foldable (foldMap)
import qualified Data.Map.Strict as Map
import           Data.Monoid (mappend)
import qualified Data.Set as Set
import qualified Data.Text as T


-- Expand Actions --------------------------------------------------------------

-- | Expand out instances of an operator, based on the types of its parameters.
-- This is similar to the case of existential elimination covered lower down.
expandActions :: TypeMap Name -> Operator -> [(ArgEnv,Operator)]
expandActions types op @ Operator { .. }

  | null opParams =
    return (Map.empty, op)

  | otherwise     =
    do (env,args) <- params opParams
       let op' = Operator { opName    = T.intercalate "-" (opName : args)
                          , opDerived = True
                          , opParams  = []
                          , ..
                          }
       return (env, op')

  where

  params (Typed { .. } : ps) =
    do (env,args) <- params ps
       e          <- lookupType tType types
       return (Map.insert tValue (AName e) env, e : args)

  params [] = return (Map.empty, [])


-- Quantifiers -----------------------------------------------------------------

-- | Remove quantifiers used in the preconditions and effects of an operator, by
-- turning forall into conjuction, and exists into disjunction.
--
-- INVARIANT: This stage removes the TForall and TExists constructors from the
-- pre and post conditions.
removeQuantifiers :: TypeMap Name -> ArgEnv -> Operator -> Operator
removeQuantifiers types env Operator { .. } =
  Operator { opPrecond = rqTerm types env opPrecond
           , opEffects = rqEff  types env opEffects
           , ..
           }

type ArgEnv = Map.Map Name Arg

-- | Remove quantifiers from effects.
rqEff :: TypeMap Name -> ArgEnv -> Effect -> Effect
rqEff types env0 = EAnd . go env0
  where
  go env (EForall xs e) =
    do env' <- params xs env
       go env' e

  go env (EAnd es) =
       EAnd `fmap` mapM (go env) es

  go env (EWhen p qs) =
       return (EWhen (rqTerm types env p) (map (substLit env) qs))

  go env (ELit l) =
       return (ELit (substLit env l))

  params (Typed { .. } : ps) env =
    do e <- lookupType tType types
       params ps (Map.insert tValue (AName e) env)
  params [] env = return env

-- | Remove quantifiers from terms.
rqTerm :: TypeMap Name -> ArgEnv -> Term -> Term
rqTerm types = go
  where
  go env (TAnd ts)      = TAnd (map (go env) ts)
  go env (TOr  ts)      = TOr  (map (go env) ts)
  go env (TNot t)       = TNot (go env t)
  go env (TImply p q)   = TImply (go env p) (go env q)
  go env (TForall xs p) = TAnd [ go env' p | env' <- params xs env ]
  go env (TExists xs p) = TOr  [ go env' p | env' <- params xs env ]
  go env (TLit a)       = TLit (substLit env a)

  params (Typed { .. } : ps) env =
    do e <- lookupType tType types
       params ps (Map.insert tValue (AName e) env)

  params [] env = return env

substLit :: ArgEnv -> Literal -> Literal
substLit env (LNot  a) = LNot  (substAtom env a)
substLit env (LAtom a) = LAtom (substAtom env a)

substAtom :: ArgEnv -> Atom -> Atom
substAtom env (Atom s as) = Atom s (map subst as)
  where
  subst arg = case arg of
    AName _ -> arg
    AVar  n -> Map.findWithDefault arg n env


-- Disjunctive Preconditions ---------------------------------------------------

-- | Generate multiple operators, corresponding to which branch of the
-- disjunction was found to be true.
--
-- INVARIANT: This stage removes the TOr, TNot, and TImply constructors.
removeDisjunction :: Operator -> [Operator]
removeDisjunction Operator { .. } =
  case rdOper of
    [res] -> return (mkOper res)
    _     ->  zipWith mkNewOper [1 ..] rdOper
  where

  rdOper = do pre <- rdTerm   (nnfTerm   opPrecond)
              eff <- rdEffect (nnfEffect opEffects)
              return (pre,eff)

  mkNewOper ix res =
    (mkOper res) { opName = T.concat [ opName, "-", T.pack (show (ix :: Int)) ] }


  mkOper (pre,eff) =
    Operator { opPrecond = pre
             , opEffects = eff
             , opDerived = True
             , .. }

-- | Remove disjunctions, by producing multiple terms.
rdTerm :: Term -> [Term]
rdTerm (TAnd ts)       = TAnd `fmap` mapM rdTerm ts
rdTerm (TOr ts)        = msum (map rdTerm ts)
rdTerm a@TLit{}        = return a
rdTerm TNot{}          = error "rdTerm: TNot"
rdTerm TImply{}        = error "rdTerm: TImply"
rdTerm TExists{}       = error "rdTerm: TExists"
rdTerm TForall{}       = error "rdTerm: TForall"

rdEffect :: Effect -> [Effect]
rdEffect (EWhen t q) = do p <- rdTerm t
                          return (EWhen p q)
rdEffect (EAnd es)   =    EAnd `fmap` map rdEffect es
rdEffect e@ELit{}    =    return e
rdEffect EForall{}   = error "nnfEffect: EForall"

-- | Put a term in negation normal form, pushing all negations down to the
-- literals.
--
-- INVARIANT: This stage removes the TNot constructor by pushing all negations
-- down to the TLit leaves, and the TImply constructor by translating it to
-- disjunction and negation.
nnfTerm :: Term -> Term

nnfTerm (TNot (TNot t))     = nnfTerm t
nnfTerm (TNot (TAnd ts))    = TOr  (map (nnfTerm . TNot) ts)
nnfTerm (TNot (TOr  ts))    = TAnd (map (nnfTerm . TNot) ts)
nnfTerm (TNot (TImply p q)) = TAnd [nnfTerm p, nnfTerm (TNot q)]
nnfTerm (TNot (TLit l))     = TLit (negLit l)

nnfTerm (TAnd ts)           = TAnd (map nnfTerm ts)
nnfTerm (TOr  ts)           = TOr  (map nnfTerm ts)
nnfTerm (TImply p q)        = TOr  [ nnfTerm (TNot p) , nnfTerm q ]

nnfTerm t@TLit{}            = t

nnfTerm (TNot TForall{})    = error "nnfTerm: TForall"
nnfTerm (TNot TExists{})    = error "nnfTerm: TExists"
nnfTerm TForall{}           = error "nnfTerm: TForall"
nnfTerm TExists{}           = error "nnfTerm: TExists"

nnfEffect :: Effect -> Effect
nnfEffect (EWhen p q) = EWhen (nnfTerm p) q
nnfEffect (EAnd es)   = EAnd (map nnfEffect es)
nnfEffect e@ELit{}    = e
nnfEffect EForall{}   = error "nnfEffect: EForall"

-- | Negate a literal
negLit :: Literal -> Literal
negLit (LAtom a) = LNot  a
negLit (LNot  a) = LAtom a


-- Negation --------------------------------------------------------------------

-- | Remove negations through the addition of special `not` predicates.  These
-- generated predicates have the same structure as their counterparts, but imply
-- the presence of the negated effect.
--
-- INVARIANT: This stage removes all negative literals from the preconditions of
-- operators and conditional effects, replacing them with other literals that
-- correspond to their negation.
removeNegation :: Problem -> [Operator] -> (Problem,[Operator])
removeNegation prob ops
  | Set.null negs = (prob,ops)
  | otherwise     = (prob', map (cnOper negs) ops)
  where

  -- the set of predicates that are are used as negative preconditions
  negs = foldMap negPreconds ops

  -- initialize the negated atoms, if their counterparts are missing from the
  -- initial state
  prob' = prob { probInit = initNegs negs (probInit prob) }

-- | Generate the initial state, given the set of atoms that show up as negative
-- preconditions, and the existing initial state.
initNegs :: Set.Set Atom -> [Literal] -> [Literal]

-- pass non-negative atoms through, that are mentioned in the initial state
initNegs negs (LAtom a : ls)
  | a `Set.member` negs = LAtom a : initNegs (Set.delete a negs) ls
  | otherwise           = LAtom a : initNegs               negs  ls

-- we can safely remove negative initial conditions that aren't used as negative
-- preconditions
initNegs negs (LNot a : ls)
  | a `Set.member` negs = LAtom (negAtom a) : initNegs (Set.delete a negs) ls
  | otherwise           =                     initNegs (Set.delete a negs) ls

-- the remaining set of atoms are depended on as negative preconditions, but
-- unset in the initial state.  their negative variants are set.
initNegs negs [] =
  [ LAtom (negAtom a) | a <- Set.toList negs ]


negPreconds :: Operator -> Set.Set Atom
negPreconds Operator { .. } = mappend (negTerms   opPrecond)
                                      (negEffects opEffects)

negTerms :: Term -> Set.Set Atom
negTerms (TAnd ts)       = foldMap negTerms ts
negTerms (TLit (LNot a)) = Set.singleton a
negTerms TLit{}          = Set.empty
negTerms TNot{}          = error "negTerms: TNot"
negTerms TForall{}       = error "negTerms: TForall"
negTerms TExists{}       = error "negTerms: TExists"
negTerms TOr{}           = error "negTerms: TOr"
negTerms TImply{}        = error "negTerms: TImply"

-- | The set of atoms used as negative preconditions for conditional effects.
negEffects :: Effect -> Set.Set Atom
negEffects (EAnd es)   = foldMap negEffects es
negEffects (EWhen p _) = negTerms p
negEffects _           = Set.empty


cnOper :: Set.Set Atom -> Operator -> Operator
cnOper negs Operator { .. } =
  Operator { opPrecond = cnTerms opPrecond
           , opEffects = cnEffects negs opEffects
           , .. }

-- | Convert all dependencies on !p to dependencies on not-p.
cnTerms :: Term -> Term
cnTerms (TAnd ts) = TAnd (map cnTerms ts)
cnTerms (TLit l)  = TLit (cnLiteral l)
cnTerms TNot{}    = error "cnTerm: TNot"
cnTerms TForall{} = error "cnTerm: TForall"
cnTerms TExists{} = error "cnTerm: TExists"
cnTerms TOr{}     = error "cnTerm: TOr"
cnTerms TImply{}  = error "cnTerm: TImply"

cnEffects :: Set.Set Atom -> Effect -> Effect
cnEffects negs = go
  where
  go (EAnd es)    = EAnd (map go es)
  go (EWhen p ls) = EWhen (cnTerms p) (concatMap adjust ls)
  go (ELit l)     = mkEAnd (map ELit (adjust l))
  go _            = error "cnEffects"

  -- this is an add effect, so assert the atom, and delete its negated version
  adjust l@(LAtom a)
    | a `Set.member` negs = [ l, LNot (negAtom a) ]

  -- this is a delete effect, so remove the atom, and assert its negated version
  adjust l@(LNot a)
    | a `Set.member` negs = [ l, LAtom (negAtom a) ]

  adjust l = [l]

-- | Convert negative literals to positive ones of the form ``$not-p''.
cnLiteral :: Literal -> Literal
cnLiteral (LNot a) = LAtom (negAtom a)
cnLiteral l        = l

negAtom :: Atom -> Atom
negAtom (Atom a as) = Atom (T.append "$not-" a) as
