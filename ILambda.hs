{-# LANGUAGE MultiParamTypeClasses, Rank2Types, ImpredicativeTypes,
  FlexibleContexts #-}

module ILambda where
-- import Control.Arrow
-- import Control.Monad
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import InteractiveProof
import InteractiveProof.Lambda
import qualified InteractiveProof.Lambda.LambdaB as LB
import InteractiveProof.ProofTree
-- import Data.List
import Data.Maybe
import Data.Tree
import Control.Lens hiding (Context)

import Text.Parsec
import Text.Parsec.String

-- newtype Variable = Variable String
--           deriving (Show, Eq, Ord, Read)

type RedexDialog a = a -> [String] -> IO Int

interactiveEvalStep :: (Show a, LambdaContext a b) => RedexDialog a -> [(String, ReductionStep a)] -> a -> IO (String, Pos, a)
interactiveEvalStep dilg steps t = do
    let rs = allRedexes steps t
    ind <- dilg t $ map (\(Redex (n,_,p))-> show n ++ ": " ++ show p) rs
    let (Redex (n, s, pos)) = rs!!ind
    return (n, pos, fromJust $ reduction s t pos)

interactiveEval :: (Show a, LambdaContext a b) => RedexDialog a -> [(String, ReductionStep a)] -> a -> [(String, Pos, a)] -> IO (a, [(String, Pos, a)])
interactiveEval dilg steps t acc = do
    let rs = concatMap (flip redexes t . (^._2)) steps
    if null rs then putStrLn "No redexes." >> return (t, reverse acc) else interactiveEvalStep dilg steps t >>= \(n, p, t') -> interactiveEval dilg steps t' ((n, p, t):acc)

-- oldLambdaEval :: IO ()
-- oldLambdaEval = do
--     putStrLn "Lambda Term"
--     t <- parseLine putStrLn getLine "LambdaTerm" LB.parseTerm
--     (r, rs) <- interactiveEval chooseRule LB.steps t []
--     print r
--     print rs

lTree :: (Show a, Statement a, Rule a (Redex a), LambdaContext a c, Formattable a (TextFormat String))=> [(String, ReductionStep a)] -> a -> IO (Maybe (ProofTree (a, Redex a)))
lTree steps = makeTree putStrLn ask rules
  where
    rules t = [Redex ("abort", ReductionStep normal, [] )] ++ allRedexes steps t
    ask _ _ [] = return Nothing
    ask n t choices = do
      ind <- chooseRule n t $ map ruleDescription choices
      return $ if ind < 0 then Nothing else Just $ choices!!ind
    normal t = Just t

main :: IO ()
main = do
    putStrLn "Lambda Term"
    t <- parseLine putStrLn getLine "LambdaTerm" LB.parseTerm
    tr <- lTree LB.steps t
    print tr
