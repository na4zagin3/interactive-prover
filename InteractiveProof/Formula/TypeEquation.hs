{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  GADTs #-}
module InteractiveProof.Formula.TypeEquation (Type (..), parseType, textSymbol, texSymbol, TypeSymbols) where

import InteractiveProof
import InteractiveProof.Formula
import InteractiveProof.Type
import Text.Parsec
-- import Control.Monad
-- import Control.Arrow
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((*>),(<*))
import Control.Lens

newtype Equation t = Equation (String, t)
          deriving (Show, Read, Eq, Ord)

instance (Type t)=>Formula (Equation t) where
    parseFormula = parseEqn textSymbol

type TypeSymbols = (String, String, String, String, String)

{-
instance Formattable Type (TextFormat String) where
    toFormat = fmap TextFormat $ showType textSymbol
    parseFormat = parseType textSymbol

instance Formattable Type (TexFormat String) where
    toFormat t = TexFormat $ "\\ensuremath{" ++ showType texSymbol t ++ "}"
    parseFormat = parseType texSymbol

showType :: TypeSymbols -> Type -> String
showType ss (Prim v) = ss^._3 ++ ss^._1 ++ v ++ ss^._2
showType ss (Var v) = ss^._4 ++ ss^._1 ++ v ++ ss^._2
showType ss (Func t1 t2) = (if t1 < Func Bot Bot then id else paren) (showType ss t1) ++ " " ++ ss^._5 ++ " " ++ showType ss t2
-}

textSymbol :: TypeSymbols
textSymbol = ("", "", "", "", "->")

texSymbol :: TypeSymbols
texSymbol = ("{", "}", "\\textbf", "\\textit", "\\to")

parseEqn :: (Type t, Stream b m Char) => TypeSymbols -> ParsecT b u m (Equation t)
parseEqn ss = pType
    where
      pVar c h = do
        string $ ss^._3
        string $ ss^._1
        vh <- h
        v <- many1 letter
        string $ ss^._2
        return $ c (vh:v)
      pType = do
        v <- pVar id letter <* spaces
        string ":" <* spaces
        t <- parseType
        return $ Equation (v, t)

