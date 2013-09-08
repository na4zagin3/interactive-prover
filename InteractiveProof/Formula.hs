{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, Rank2Types, ImpredicativeTypes #-}
module InteractiveProof.Formula ( Formula, parseFormula
                                , Sequent(..), InferRule(..), ApplicableRule(..), singleton, formatUsageStr
                                , parseStep, delimited
                                , iden
                                , contrL, contrR, weakL, weakR, moveLR, moveRL
                                , leftTermSingle, leftTermDouble, rightTermSingle, rightTermDouble
                                ) where

import InteractiveProof
import InteractiveProof.ProofTree
import Control.Applicative ((<*),(*>))
import Control.Monad
import Data.String
import Data.List
import Data.Monoid
import Data.Maybe
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MS
import Text.Parsec


class Formula a where
    parseFormula :: Stream b m Char => ParsecT b u m a

data Sequent a = Sequent (MultiSet a, MultiSet a)
                  deriving (Show, Eq, Ord)

instance (Formula a)=>Statement (Sequent a)


instance (Formattable a (TextFormat String), Ord a)=>Formattable (Sequent a) (TextFormat String) where
  toFormat (Sequent (l, r)) = TextFormat $ conv l ++ " |- " ++ conv r
      where
        conv ms = intercalate ", " (map ((\(TextFormat x) -> x) .  toFormat) (MS.toList ms))
  parseFormat = do
        ls <- many (parseFormat <* spaces <* string "," <* spaces)
        string "|-" >> spaces
        rs <- many (parseFormat <* spaces <* string "," <* spaces)
        return $ Sequent (MS.fromList ls, MS.fromList rs)

instance (Formattable a (TexFormat String), Ord a)=>Formattable (Sequent a) (TexFormat String) where
  toFormat (Sequent (l, r)) = TexFormat $ "\\ensuremath{" ++ conv l ++ " \\vdash " ++ conv r ++ "}"
      where
        conv ms = intercalate ", " (map ((\(TexFormat x) -> x) .  toFormat) (MS.toList ms))
  parseFormat = do
        ls <- many (parseFormat <* spaces <* string "," <* spaces)
        string "\\vdash" >> spaces
        rs <- many (parseFormat <* spaces <* string "," <* spaces)
        return $ Sequent (MS.fromList ls, MS.fromList rs)


singleton :: a -> Sequent a
singleton a = Sequent (MS.empty, MS.singleton a)

instance (Formula a)=> Rule (Sequent a) (ApplicableRule a) where
    ruleDescription (ApplicableRule (n, d, _)) = "Rule " ++ n ++ " " ++ d
    applyRule (ApplicableRule (_, _, r)) t = fromJust $ r t
    applicableRule (ApplicableRule (_, _, r)) t = isJust $ r t

data InferRule a = StructureRule (Sequent a -> Maybe [Sequent a])
                 | VariableRule ([Variable] -> Sequent a -> Maybe [Sequent a])
                 | FormulaRule (a -> Sequent a -> Maybe [Sequent a])
                 | FormulaeRule (a -> (MultiSet a, MultiSet a) -> Sequent a -> Maybe [Sequent a])
                 | FreeFormatRule (String, Stream b m Char=> ParsecT b u m (String, Sequent a -> Maybe [Sequent a]))

formatUsageStr :: InferRule a -> String
formatUsageStr (StructureRule _) = ""
formatUsageStr (VariableRule _) = " vs.."
formatUsageStr (FormulaRule _) = "(t)"
formatUsageStr (FormulaeRule _) = "(t)[l..][r..]"
formatUsageStr (FreeFormatRule (fmt,_)) = fmt

instance (Formattable a (TextFormat String))=> Formattable (ApplicableRule a) (TextFormat String) where
    toFormat (ApplicableRule(r, "", _)) = TextFormat r
    toFormat (ApplicableRule(r, arg, _)) = TextFormat $ r ++ " " ++ arg
    parseFormat = undefined

instance (Formattable a (TexFormat String))=> Formattable (ApplicableRule a) (TexFormat String) where
    toFormat (ApplicableRule(r, "", _)) = TexFormat $ "\\texttt{" ++ r ++ "}"
    toFormat (ApplicableRule(r, arg, _)) = TexFormat $ "\\texttt{" ++ r ++ " " ++ arg ++ "}"
    parseFormat = undefined

instance (Formula a, Formattable a (TextFormat String), Ord a)=> Formattable (Sequent a, ApplicableRule a) (TextFormat String) where
    toFormat (s, r) = toFormat s `mappend` return " " `mappend` parenM (toFormat r)
    parseFormat = do
      s <- parseFormat <* spaces
      r <- parseFormat
      return (s, r)

newtype ApplicableRule a = ApplicableRule (String, String, Sequent a -> Maybe [Sequent a])


instance Show (ApplicableRule a) where
    show (ApplicableRule (n, d, _)) = paren $ "ApplicableRule " ++ n ++ " " ++ d

--    parseFormat :: Stream b m Char => ParsecT b u m a
parseStep :: (IsString String, Ord a, Stream b m Char, Formattable a b, Formattable a (TextFormat String), Formula a)=> Sequent a -> [(String, InferRule a)] -> ParsecT b u m (ApplicableRule a)
parseStep _ ss = do
      rn <- many1 parseIdChar <* spaces
      case lookup (toString rn) ss of
        Nothing -> unexpected ("step name:" ++ toString rn)
        Just (StructureRule r) -> return $ ApplicableRule (rn, "", r)
        Just (VariableRule r) -> do
          vs <- pVars
          return $ ApplicableRule (rn, toString $ mconcat $ intersperse " " $ map toString vs, r vs)
        Just (FormulaRule r) -> do
          f <- string "(" *> pTerm <* string ")"
          return $ ApplicableRule (rn, toString' $ parenM (toFormat f :: TextFormat String), r f)
        Just (FormulaeRule r) -> do
          f <- string "(" *> pTerm <* string ")" <* spaces
          ls <- delimited (string "[" >> spaces) (string "," >> spaces) pTerm (string "]" >> spaces) <* spaces
          rs <- delimited (string "[" >> spaces) (string "," >> spaces) pTerm (string "]" >> spaces)
          return $ ApplicableRule (rn, toString' . mconcat $ [parenM (toFormat f :: TextFormat String), return " [", strSeq ls, return "] [", strSeq rs, return "]"], r f (MS.fromList ls, MS.fromList rs))
        Just (FreeFormatRule (_, mr)) -> do
          r <- mr
          return $ ApplicableRule (rn, fst r, snd r)
    where
      pVars = many1 $  many1 parseIdChar <* spaces
      pTerm = parseFormat
      strSeq fs = mconcat $ intersperse (return ", " :: TextFormat String) $ map toFormat fs
      toString' :: (IsString String)=> TextFormat String -> String
      toString' = toString

delimited :: Stream b m Char => ParsecT b u m c -> ParsecT b u m d -> ParsecT b u m a -> ParsecT b u m e -> ParsecT b u m [a]
delimited l s p r = l >> (((p >>= \h -> liftM (h:) (many (s *> p)) <|> liftM return p ) <* r) <|> (r >> return []))


iden :: (Ord a)=>Sequent a -> Maybe [Sequent a]
iden (Sequent (l,r)) | MS.size l == 1 && MS.size r == 1 && MS.null (l MS.\\ r) = Just []
                     | otherwise                                            = Nothing

contrL :: (Ord a)=>a -> Sequent a -> Maybe [Sequent a]
contrL t (Sequent (l,r)) | t `MS.member` l = Just [Sequent (MS.insert t l, r)]
                         | otherwise       = Nothing

contrR :: (Ord a)=>a -> Sequent a -> Maybe [Sequent a]
contrR t (Sequent (l,r)) | t `MS.member` r = Just [Sequent (l, MS.insert t r)]
                         | otherwise       = Nothing

weakL :: (Ord a)=>a -> Sequent a -> Maybe [Sequent a]
weakL t (Sequent (l,r)) | t `MS.member` l = Just [Sequent (MS.delete t l, r)]
                        | otherwise       = Nothing

weakR :: (Ord a)=>a -> Sequent a -> Maybe [Sequent a]
weakR t (Sequent (l,r)) | t `MS.member` r = Just [Sequent (l, MS.delete t r)]
                        | otherwise       = Nothing

moveRL :: (Ord a)=>a -> Sequent a -> Maybe [Sequent a]
moveRL t (Sequent (l,r)) | t `MS.member` r = Just [Sequent (MS.insert t l, MS.delete t r)]
                         | otherwise       = Nothing

moveLR :: (Ord a)=>a -> Sequent a -> Maybe [Sequent a]
moveLR t (Sequent (l,r)) | t `MS.member` l = Just [Sequent (MS.delete t l, MS.insert t r)]
                         | otherwise       = Nothing

leftTermSingle :: (Ord a)=>(a -> Sequent a -> Maybe [Sequent a]) -> a -> Sequent a -> Maybe [Sequent a]
leftTermSingle f t (Sequent (l,r)) | t `MS.member` l = f t $ Sequent (MS.delete t l,r)
                             | otherwise       = Nothing

rightTermSingle :: (Ord a)=>(a -> Sequent a -> Maybe [Sequent a]) -> a -> Sequent a -> Maybe [Sequent a]
rightTermSingle f t (Sequent (l,r)) | t `MS.member` r = f t $ Sequent (l,MS.delete t r)
                              | otherwise       = Nothing

leftTermDouble :: (Ord a)=>(a -> Sequent a -> Sequent a -> Maybe [Sequent a]) -> a -> (MultiSet a, MultiSet a) -> Sequent a -> Maybe [Sequent a]
leftTermDouble f t (ls,rs) (Sequent (l,r)) | t `MS.member` l && ls `MS.isSubsetOf` l' && rs `MS.isSubsetOf` r = f t (Sequent (ls, rs)) (Sequent (l' MS.\\ ls, r MS.\\ rs))
                                      | otherwise       = Nothing
                                      where
                                        l' = MS.delete t l

rightTermDouble :: (Ord a)=>(a -> Sequent a -> Sequent a -> Maybe [Sequent a]) -> a -> (MultiSet a, MultiSet a) -> Sequent a -> Maybe [Sequent a]
rightTermDouble f t (ls,rs) (Sequent (l,r)) | t `MS.member` r && ls `MS.isSubsetOf` l && rs `MS.isSubsetOf` r' = f t (Sequent (ls, rs)) (Sequent (l MS.\\ ls, r' MS.\\ rs))
                                       | otherwise       = Nothing
                                      where
                                        r' = MS.delete t r
