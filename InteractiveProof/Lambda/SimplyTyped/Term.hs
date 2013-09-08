{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}
module InteractiveProof.Lambda.SimplyTyped.Term (Term (..), parseTerm) where

import InteractiveProof
import InteractiveProof.Formula
import InteractiveProof.Type.Simple (Type, parseType)
import qualified InteractiveProof.Type.Simple as T
import Text.Parsec
import Data.Monoid
import Control.Monad
-- import Control.Arrow
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((*>),(<*))
import Control.Lens

data Term = TmBot
          | TmTrue
          | TmFalse
          | TmVar String
          | TmApp Term Term
          | TmIf Term Term Term
          | TmAbs String Type Term
          deriving (Read, Eq, Ord)

-- instance Show Term where
--     show t = paren $ toString (showTerm textSymbol t :: TextFormat String)

instance Formula Term where
    parseFormula = parseTerm textSymbol T.textSymbol

type TermSymbols = (String, String, String, String, String, String -> String, String -> String)

instance Formattable Term (TextFormat String) where
    toFormat = showTerm textSymbol
    parseFormat = parseTerm textSymbol T.textSymbol

instance Formattable Term (TexFormat String) where
    toFormat t = TexFormat "\\ensuremath{" `mappend` showTerm texSymbol t `mappend` TexFormat "}"
    parseFormat = parseTerm texSymbol T.texSymbol

textSymbol :: TermSymbols
textSymbol = ("^", ".", "True", "False", " ", id, id)

texSymbol :: TermSymbols
texSymbol = ("\\lambda ", ".", "True", "False", "\\ ", \x -> "\\mathop{\\mathrm{" ++ x ++ "}}", \x -> "\\mathit{" ++ x ++ "}")

parenIfNot :: Bool -> String -> String
parenIfNot b = if b then id else paren

showTerm :: (Formattable Type (m String), Monad m, Monoid (m String))=>TermSymbols -> Term -> m String
showTerm ss TmTrue = return $ ss^._3
showTerm ss TmFalse = return $ ss^._4
showTerm ss (TmVar v) = return (ss^._7 $ v)
showTerm ss (TmApp tm1 tm2) = mconcat [ liftM (parenIfNot (tm1 < TmIf TmBot TmBot TmBot)) $ showTerm ss tm1
                                      , return " "
                                      , liftM (parenIfNot (tm2 < TmApp TmBot TmBot)) $ showTerm ss tm2]
showTerm ss (TmIf tm1 tm2 tm3) = mconcat [ return $ (ss^._6 $ "if")++ " "
                                         , showTerm ss tm1
                                         , return $ " " ++ (ss^._6 $ "then") ++ " "
                                         , showTerm ss tm2
                                         , return $ " " ++ (ss^._6 $ "else")
                                         , showTerm ss tm3]
showTerm ss (TmAbs v ty tm) = mconcat [ return $ ss^._1 ++ v ++ ":"
                                      , toFormat ty
                                      , return $ ss^._2 ++ ss^._5
                                      , showTerm ss tm]

parseTerm :: (Stream b m Char) => TermSymbols -> T.TypeSymbols -> ParsecT b u m  Term
parseTerm ss tss = pTerm
    where
      pVar = notFollowedBy ((string "if" <|> string "then" <|> string "else") >> notFollowedBy alphaNum) >> liftM TmVar (many1 parseIdChar)
      pTrue = try (string (ss^._3) >> return TmTrue)
      pFalse = try (string (ss^._4) >> return TmFalse)
      pAtom = (string "(" >> pTerm <* string ")") <|> pTrue <|> pFalse <|> pVar
      pFactor = do
        t1 <- pAtom <* spaces
        t2 <- many $ pAtom <* spaces
        return $ unfoldL TmApp t1 t2
      pIf = do
        string "if" <* spaces
        t1 <- pTerm <* spaces
        string "then" <* spaces
        t2 <- pTerm <* spaces
        string "else" <* spaces
        t3 <- pTerm
        return $ TmIf t1 t2 t3
      pAbs = do
        (string "^" <|> string "λ") <* spaces
        v <- many1 parseIdChar <* spaces
        string ":" <* spaces
        ty <- parseType tss <* spaces
        string "." <* spaces
        tm <- pTerm
        return $ TmAbs v ty tm
      pTerm = pAbs <|> pIf <|> pFactor
