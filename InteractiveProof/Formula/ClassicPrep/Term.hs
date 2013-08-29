{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module InteractiveProof.Formula.ClassicPrep.Term (Term (..), parseTerm) where

import InteractiveProof
import InteractiveProof.Formula
import Text.Parsec
import Control.Monad
-- import Control.Arrow
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((*>),(<*))
import Control.Lens

data Term = Bot
          | Var Variable
          | Not Term
          | And Term Term
          | Or Term Term
          | Imp Term Term
          deriving (Read, Eq, Ord)

instance Show Term where
    show = paren . showTerm textSymbol

instance Formula Term where
    parseFormula = parseTerm textSymbol

type TermSymbols = (String, String, String, String, String)

instance Formattable Term (TextFormat String) where
    toFormat = fmap TextFormat $ showTerm textSymbol
    parseFormat = parseTerm textSymbol

instance Formattable Term (TexFormat String) where
    toFormat t = TexFormat $ "\\ensuremath{" ++ showTerm texSymbol t ++ "}"
    parseFormat = parseTerm texSymbol

textSymbol :: TermSymbols
textSymbol = ("_", "~", "/\\", "\\/", "->")

texSymbol :: TermSymbols
texSymbol = ("\\bot", "\\lnot", "\\land", "\\lor", "\\to")

showTerm :: TermSymbols -> Term -> String
showTerm ss Bot = ss^._1
showTerm _  (Var v) = v
showTerm ss (Not t) = ss^._2 ++ " " ++ (if t < Not Bot then id else paren) (showTerm ss t)
showTerm ss (And t1 t2) = (if t1 < Or Bot Bot then id else paren) (showTerm ss t1) ++ " " ++ ss^._3 ++ " " ++ (if t2 < And Bot Bot then id else paren) (showTerm ss t2)
showTerm ss (Or t1 t2) = (if t1 < Imp Bot Bot then id else paren) (showTerm ss t1) ++ " " ++ ss^._4 ++ " " ++ (if t2 < Or Bot Bot then id else paren) (showTerm ss t2)
showTerm ss (Imp t1 t2) = (if t1 < Imp Bot Bot then id else paren) (showTerm ss t1) ++ " " ++ ss^._5 ++ " " ++ showTerm ss t2

parseTerm :: Stream b m Char => TermSymbols -> ParsecT b u m  Term
parseTerm ss = pTerm
    where
      pVar = liftM Var $ many1 letter
      pBot = string (ss^._1) >> return Bot
      pNot = do
        string (ss^._2) <* spaces
        t <- pAtom
        return $ Not t
      pAtom = (string "(" >> pTerm <* string ")") <|> pNot <|> pBot <|> pVar
      pAnd = do
        t1 <- pAtom <* spaces
        t2 <- many $ string (ss^._3) >> spaces *> pAtom
        return $ unfoldL And t1 t2
      pOr = do
        t1 <- pAnd <* spaces
        t2 <- many $ string (ss^._4) >> spaces *> pAnd
        return $ unfoldL Or t1 t2
      pImp = do
        t1 <- pOr <* spaces
        t2 <- many $ string (ss^._5) >> spaces *> pOr
        return $ unfoldR Imp t1 t2
      pTerm = pImp

