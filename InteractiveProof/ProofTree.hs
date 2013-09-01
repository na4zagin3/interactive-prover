{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving #-}

module InteractiveProof.ProofTree where

-- import Control.Monad
import Prelude hiding (concat)
import InteractiveProof
import Data.Foldable
import Data.Monoid
import Data.Tree 
import Data.Maybe 
import Text.Parsec

class Statement a

newtype ProofTree a = ProofTree (Tree a)
                deriving (Show, Eq)

newtype AnnotatedProofTree a = AnnotatedProofTree (ProofTree a)
                deriving (Show, Eq)

type CandidateRule a = a -> Maybe [a]

-- type Rule a = a -> [a]
class Rule a b | b -> a where
--    ruleName :: Rule a -> String
    ruleDescription :: (Rule a b)=> b -> String
    applyRule :: (Statement a, Rule a b)=> b -> a -> [a]
    applicableRule :: (Statement a, Rule a b)=> b -> a -> Bool

instance Formattable a (TextFormat String) => Formattable (ProofTree a) (TextFormat String) where
    toFormat (ProofTree t) = fitchStyle 1 t
    parseFormat = parseFitchTree

instance (Statement a, Formattable a (TexFormat String)) => Formattable (ProofTree a) (TexFormat String) where
    toFormat (ProofTree t) = bussproof 0 t
    parseFormat = undefined

instance (Formattable a (TextFormat String), Formattable b (TextFormat String)) => Formattable (AnnotatedProofTree (a,b)) (TextFormat String) where
    toFormat (AnnotatedProofTree (ProofTree t)) = fitchStyle 1 (fmap (\(a,b)-> toString $ mconcat [parenM $ toFormat b :: TextFormat String, return "\t", toFormat a]) t :: Tree String)
    parseFormat = undefined

instance (Formattable a (TexFormat String), Formattable b (TexFormat String)) => Formattable (AnnotatedProofTree (a,b)) (TexFormat String) where
    toFormat (AnnotatedProofTree (ProofTree t)) = bussproofAnnot 0 t
    parseFormat = undefined

parseFitchTree :: (Stream s m Char, Formattable a s) => ParsecT s u m (ProofTree a)
parseFitchTree = do
    ls <- many1 $ do
      ind <- many spaces
      t <- parseFormat
      return (length ind, t)
    let (t:ts) = reverse ls
    return $ ProofTree $ unfoldFitchTree t ts

fitchStyle :: (Formattable a (m String), Monoid (m String), Monad m)=> Int -> Tree a -> m String
-- fitchStyle (Node t []) n = take n (repeat ' ') ++ toFormat t
fitchStyle n (Node t xs) = mconcat [children, indent, content]
    where
      children = mconcat $ map (\x -> fitchStyle (n+1) x `mappend` return "\n") xs
      indent = mconcat $ map return (replicate (n-1) "| " `mappend` ["+ "])
      content = toFormat t

bussproof :: (Formattable a (m String), Monoid (m String), Monad m)=> Int -> Tree a -> m String
-- fitchStyle (Node t []) n = take n (repeat ' ') ++ toFormat t
bussproof n (Node t xs) = mconcat [children, indent, content]
    where
      children = mconcat $ map (\x -> bussproof (n+1) x `mappend` return "\n") xs
      indent = return $ concat $ replicate n "  "
      insn = mconcat $ map return ["\\", ["AxiomC", "BinaryInfC", "TenaryInfC"] !! length xs]
      content = mconcat [insn, return "{", toFormat t, return "}"]

bussproofAnnot :: (Formattable a (m String), Formattable b (m String), Monad m)=> Int -> Tree (a, b) -> m String
-- fitchStyle (Node t []) n = take n (repeat ' ') ++ toFormat t
bussproofAnnot n (Node (t,l) ts) = mconcat [children, indent n, insn]
    where
      nchild = length ts
      children = if nchild == 0 then indent (n+1) `mappend` return "\\AxiomC{}\n" else mconcat $ map (\x -> bussproofAnnot (n+1) x `mappend` return "\n") ts
      indent i = return $ concat $ replicate i "  "
      insn = mconcat [return "\\RightLabel{", toFormat l, return "}\\", return (["UnaryInfC", "UnaryInfC", "BinaryInfC", "TrinaryInfC"] !! nchild), return "{", toFormat t, return "}"]

unfoldFitchTree :: Ord t => (t, a) -> [(t, a)] -> Tree a
unfoldFitchTree (_, t) [] = Node t []
unfoldFitchTree (_, t) ts = Node t ts'
    where
      ts' = map (\(x:xs) -> unfoldFitchTree x xs) $ unfoldIndentedTree ts

unfoldIndentedTree :: Ord t => [(t, a)] -> [[(t, a)]]
unfoldIndentedTree [] = []
unfoldIndentedTree ((n, t):ts) = case span (\(n', _) -> n' > n) ts of
                                      (h', ts') -> ((n, t):h') : unfoldIndentedTree ts'

showInteger :: Integer -> String
showInteger = show

takeWhileM :: (Monad m)=> (a -> Bool) -> [m a] -> m (Bool, [a])
takeWhileM _ [] = return (True, [])
takeWhileM f (x:xs) = do
    v <- x
    if f v then takeWhileM f xs >>= (\(b, vs)-> return (b, v:vs)) else return (False, [])

allOrNothingM :: (Functor m, Monad m)=> (a -> Bool) -> [m a] -> m (Maybe [a])
allOrNothingM f xs = fmap g $ takeWhileM f xs
    where
      g (False, _) = Nothing
      g (True, xs') = Just xs'

allJustM :: (Functor m, Monad m)=> [m (Maybe a)] -> m (Maybe [a])
allJustM xs = fmap (fmap catMaybes) $ allOrNothingM isJust xs

makeTree' :: (Monad m, Functor m, Statement a, Rule a b)=> (String -> m ()) -> (Int -> a -> [b] -> m (Maybe b)) -> (a -> [b]) -> Int -> a -> m (Maybe (Tree (a, b)))
makeTree' putLn ask rules n c = do
    let choices = rules c
    rule <- ask n c choices
    case rule of
      Nothing -> return Nothing
      Just r -> f r
  where
    f rule = do
      let ps = applyRule rule c
      let goals = length ps
      pps <- allJustM $ map (\(i,c')-> makeTree' putLn ask rules (n + goals - i) c') $ zip [1..] ps
      maybe (putLn "failed." >> makeTree' putLn ask rules n c) (return . Just . Node (c, rule)) pps

makeTree :: (Monad m, Functor m, Statement a, Rule a b)=> (String -> m ()) -> (Int -> a -> [b] -> m (Maybe b)) -> (a -> [b]) -> a -> m (Maybe (ProofTree (a, b)))
makeTree putLn ask rules c = do
    ans <- makeTree' putLn ask rules 0 c
    return $ fmap ProofTree ans
