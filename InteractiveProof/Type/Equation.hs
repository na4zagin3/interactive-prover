{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module InteractiveProof.Type.Simple (Type (..), parseType, textSymbol, texSymbol, TypeSymbols) where

import InteractiveProof
import InteractiveProof.Formula
import Text.Parsec
-- import Control.Monad
-- import Control.Arrow
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((*>),(<*))
import Control.Lens

data Type = Bot
          | Prim String
          | Var Variable
          | Func Type Type
          deriving (Read, Eq, Ord)

instance Show Type where
    show = paren . showType textSymbol

instance Formula Type where
    parseFormula = parseType textSymbol

type TypeSymbols = (String, String, String, String, String)

instance Formattable Type (TextFormat String) where
    toFormat = fmap TextFormat $ showType textSymbol
    parseFormat = parseType textSymbol

instance Formattable Type (TexFormat String) where
    toFormat t = TexFormat $ "\\ensuremath{" ++ showType texSymbol t ++ "}"
    parseFormat = parseType texSymbol

textSymbol :: TypeSymbols
textSymbol = ("", "", "", "", "->")

texSymbol :: TypeSymbols
texSymbol = ("{", "}", "\\textbf", "\\textit", "\\to")

showType :: TypeSymbols -> Type -> String
showType ss (Prim v) = ss^._3 ++ ss^._1 ++ v ++ ss^._2
showType ss (Var v) = ss^._4 ++ ss^._1 ++ v ++ ss^._2
showType ss (Func t1 t2) = (if t1 < Func Bot Bot then id else paren) (showType ss t1) ++ " " ++ ss^._5 ++ " " ++ showType ss t2

parseType :: Stream b m Char => TypeSymbols -> ParsecT b u m  Type
parseType ss = pType
    where
      pVar c h = do
        string $ ss^._3
        string $ ss^._1
        vh <- h
        v <- many1 letter
        string $ ss^._2
        return $ c (vh:v)
      pAtom = (string "(" >> pType <* string ")") <|> try (pVar Var lower) <|> try (pVar Prim upper) 
      pFunc = do
        t1 <- pAtom <* spaces
        t2 <- many $ string (ss^._5) >> spaces *> pAtom
        return $ unfoldR Func t1 t2
      pType = pFunc

