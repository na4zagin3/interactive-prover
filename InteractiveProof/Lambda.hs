{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, UndecidableInstances #-}

module InteractiveProof.Lambda (Variable, Pos, LambdaTerm, LambdaContext, LocativeTree, parseLambda, subst, alpha, split, toContext, makeHole, patchHole, walk, match, subtree, var, redexes, reduction, ReductionStep(..), allRedexes, Redex(..)) where

import InteractiveProof
import InteractiveProof.ProofTree

import Data.Maybe
import Control.Lens
import Text.Parsec

type Pos = [Integer]

newtype Redex a = Redex (String, ReductionStep a, Pos)

newtype ReductionStep a = ReductionStep (a -> Maybe a)

class (Eq a, LocativeTree a) => LambdaTerm a where
    parseLambda :: String -> Either ParseError a
    var :: Variable -> a
    subst :: Variable -> a -> a -> a
    alpha :: Variable -> Variable -> a -> a

class (LambdaTerm a) => LambdaContext a b | a -> b where
    split :: a -> Pos -> Maybe (b,a)
    toContext :: a -> b
    makeHole :: a -> Pos -> Maybe b
    patchHole :: b -> a -> a
    fromContext :: b -> a

    fromContext c = patchHole c (var "dummy") 

class (Eq a) => LocativeTree a where
    walk :: (a -> Maybe a -> a) -> a -> a
    match :: (a -> Bool) -> a -> [Pos]
    subtree :: a -> Pos -> Maybe a

instance (LambdaContext a b)=> Rule a (Redex a) where
    ruleDescription (Redex (n, _, pos)) = "Redex " ++ n ++ " " ++ show pos
    applyRule (Redex (_, r, pos)) t = if t' == Just t then [] else [fromMaybe t t']
        where
          t' = reduction r t pos
    applicableRule (Redex (_, r, pos)) t = isJust $ reduction r t pos

instance (LambdaContext a b)=> Show (Redex a) where
    show = ruleDescription

redexes :: (LambdaTerm a)=> ReductionStep a -> a -> [Pos]
redexes (ReductionStep f) = match (isJust . f)

reduction :: (LambdaContext a b) => ReductionStep a -> a -> Pos -> Maybe a
reduction (ReductionStep step) t p = do
    (c, t') <- split t p
    t'' <- step t'
    return $ patchHole c t''

allRedexes :: (LambdaTerm a) => [(String, ReductionStep a)] -> a -> [Redex a]
allRedexes steps t = do
    ns <- steps
    p <- redexes (ns^._2) t
    return $ Redex (ns^._1, ns^._2, p)

-- redexName :: Redex a -> String
-- redexName (Redex (n,_,_)) = n
