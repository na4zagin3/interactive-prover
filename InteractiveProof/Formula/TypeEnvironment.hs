{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  GADTs #-}
module InteractiveProof.Formula.TypeEnvironment (TypeEnvironment(..)) where

import Data.Map(Map)
import qualified Data.Map as M
import InteractiveProof
import InteractiveProof.Formula
import InteractiveProof.Type
import Text.Parsec
import Data.Monoid
import Data.List
import Control.Monad()
-- import Control.Arrow
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((<*))
import Control.Lens

newtype TypeEnvironment t = TypeEnvironment (Map String t)
          deriving (Show, Read, Eq, Ord)

instance (Type t)=>Formula (TypeEnvironment t) where
    parseFormula = parseTyEnv textSymbol

type TypeSymbols = (String, String, String, String, String)

instance (Type t, Formattable t (TextFormat String))=>Formattable (TypeEnvironment t) (TextFormat String) where
    toFormat = showTyEnv textSymbol
    parseFormat = parseTyEnv textSymbol

instance (Type t, Formattable t (TexFormat String))=>Formattable (TypeEnvironment t) (TexFormat String) where
    toFormat = showTyEnv texSymbol
    parseFormat = parseTyEnv texSymbol

-- instance Formattable TypeEnvironment (TexFormat String) where
--     toFormat t = TexFormat $ "\\ensuremath{" ++ showTyEnv texSymbol t ++ "}"
--     parseFormat = parseTyEnv texSymbol

showTyEnv :: (Monoid (m String), Monad m, Formattable t (m String), Type t)=>TypeSymbols -> TypeEnvironment t -> m String
showTyEnv ss (TypeEnvironment vts) = mconcat [return (ss^._3), return (ss^._1), contents, return (ss^._2)]
    where
      contents = mconcat $ intersperse (return (ss^._5 ++ " ")) $ map (\(v,t) -> return v `mappend` return (ss^._4) `mappend` toFormat t) $ M.toList vts

textSymbol :: TypeSymbols
textSymbol = ("{", "}", "", ":", ",")

texSymbol :: TypeSymbols
texSymbol = ("{", "}", "\\set", ":", ",")

parseTyEnv :: (Type t, Stream b m Char) => TypeSymbols -> ParsecT b u m (TypeEnvironment t)
parseTyEnv ss = pEnv
    where
      pVar c h = do
        vh <- h
        v <- many1 parseIdChar
        return $ c (vh:v)
      pEqn = do
        v <- pVar id parseIdChar <* spaces
        string $ ss^._4
        spaces
        t <- parseType
        return (v, t)
      pEnv = do
        string $ ss^._3
        eqns <- delimited (string (ss^._1) >> spaces) (string (ss^._5) >> spaces) pEqn (string (ss^._2) >> spaces) <* spaces
        return $ TypeEnvironment $ M.fromList eqns

