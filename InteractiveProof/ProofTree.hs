{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, FlexibleInstances #-}

module InteractiveProof.ProofTree where

-- import Control.Monad
import InteractiveProof
import Data.Tree 
import Data.Maybe 
import Text.Parsec

class Statement a

newtype ProofTree a = ProofTree (Tree a)
                deriving (Show, Eq)

type CandidateRule a = a -> Maybe [a]

-- type Rule a = a -> [a]
class Rule a b | b -> a where
--    ruleName :: Rule a -> String
    ruleDescription :: (Rule a b)=> b -> String
    applyRule :: (Statement a, Rule a b)=> b -> a -> [a]
    applicableRule :: (Statement a, Rule a b)=> b -> a -> Bool

instance Formattable a (TextFormat String) => Formattable (ProofTree a) (TextFormat String) where
    toFormat (ProofTree t) = TextFormat $ fitchStyle 1 t
    parseFormat = parseFitchTree

--instance Formattable a (TexFormat String) => Formattable (ProofTree a) (TexFormat String) where
--    toFormat (ProofTree t) = TexFormat $ bussproof 0 t
--    parseFormat = undefined

instance (Formattable a (TexFormat String), Formattable b (TexFormat String)) => Formattable (ProofTree (a,b)) (TexFormat String) where
    toFormat (ProofTree t) = TexFormat $ bussproofAnnot 0 t
    parseFormat = undefined

parseFitchTree :: (Stream s m Char, Formattable a s) => ParsecT s u m (ProofTree a)
parseFitchTree = do
    ls <- many1 $ do
      ind <- many spaces
      t <- parseFormat
      return (length ind, t)
    let (t:ts) = reverse ls
    return $ ProofTree $ unfoldFitchTree t ts

fitchStyle :: (Formattable a (TextFormat String))=> Int -> Tree a -> String
-- fitchStyle (Node t []) n = take n (repeat ' ') ++ toFormat t
fitchStyle n (Node t xs) = concatMap (\x -> fitchStyle (n+1) x ++ "\n") xs ++ concat (replicate (n-1) "| " ++ ["+ "]) ++ toFormat t

bussproof :: (Formattable a (TexFormat String))=> Int -> Tree a -> String
-- fitchStyle (Node t []) n = take n (repeat ' ') ++ toFormat t
bussproof n (Node t ts) = concat (map (\x -> bussproof (n+1) x ++ "\n") ts ++ replicate n "  " ++ ["\\", ["AxiomC", "BinaryInfC", "TenaryInfC"] !! length ts, "{", toString (toFormat t :: TexFormat String), "}"])

bussproofAnnot :: (Formattable a (TexFormat String), Formattable b (TexFormat String))=> Int -> Tree (a, b) -> String
-- fitchStyle (Node t []) n = take n (repeat ' ') ++ toFormat t
bussproofAnnot n (Node (t,l) ts) = concat $ children ++ indent n ++ insn
    where
      nchild = length ts
      children = if nchild == 0 then indent (n+1) ++ ["\\AxiomC{}\n"] else map (\x -> bussproofAnnot (n+1) x ++ "\n") ts
      indent i = replicate i "  "
      insn = ["\\RightLabel{" ++ texString l ++ "}", "\\", ["UnaryInfC", "UnaryInfC", "BinaryInfC", "TriaryInfC"] !! nchild, "{", texString t, "}"]
      texString :: (Formattable a (TexFormat String))=> a -> String
      texString x = toString (toFormat x :: TexFormat String)

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

makeTree' :: (Monad m, Functor m, Statement a, Rule a b)=> (String -> m ()) -> (a -> [b] -> m (Maybe b)) -> (a -> [b]) -> a -> m (Maybe (Tree (a, b)))
makeTree' putLn ask rules c = do
    let choices = rules c
    rule <- ask c choices
    case rule of
      Nothing -> return Nothing
      Just r -> f r
  where
    f rule = do
      let ps = applyRule rule c
      pps <- allJustM $ map (makeTree' putLn ask rules) ps
      maybe (putLn "failed." >> makeTree' putLn ask rules c) (return . Just . Node (c, rule)) pps

makeTree :: (Monad m, Functor m, Statement a, Rule a b)=> (String -> m ()) -> (a -> [b] -> m (Maybe b)) -> (a -> [b]) -> a -> m (Maybe (ProofTree (a, b)))
makeTree putLn ask rules c = do
    ans <- makeTree' putLn ask rules c
    return $ fmap ProofTree ans
