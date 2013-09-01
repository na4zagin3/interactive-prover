{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
  UndecidableInstances #-}

module InteractiveProof.Lambda.SimplyTyped.TypingTree (TypingExpr,typingSteps) where

import InteractiveProof
-- import InteractiveProof.ProofTree
import InteractiveProof.Formula
import InteractiveProof.Formula.TypeEnvironment
import InteractiveProof.Lambda.SimplyTyped.Term
import InteractiveProof.Type.Simple
import Data.Monoid
import Control.Monad
-- import Control.Arrow
import Control.Applicative ((<$>),(*>),(<*),(<*>),pure)
-- import Control.Applicative ((<*))
-- import Data.Maybe
import qualified Data.MultiSet as MS
import qualified Data.Map as M
import Text.Parsec
-- import Text.Parsec.String

data TypingExpr = Env (TypeEnvironment Type)
                | Expr Term Type
                deriving (Ord, Eq)

instance Formula TypingExpr where
    parseFormula = liftM Env parseFormula <|> (Expr <$> (parseFormula <* spaces <* string ":" <* spaces) <*> parseFormula )

instance (Monoid b, Formattable Term b, Formattable Type b, Formattable String b,Formattable (TypeEnvironment Type) b)=> Formattable TypingExpr b where
    parseFormat = liftM Env parseFormat <|> (Expr <$> (parseFormula <* spaces <* string ":" <* spaces) <*> parseFormula )
    toFormat (Expr e t) = toFormat e `mappend` toFormat ":" `mappend` toFormat t
    toFormat (Env env) = toFormat env

{-
andL1, andL2, orR1, orR2, impR, notL, notR :: Term -> Sequent Term -> Maybe [Sequent Term]

andL1 (And t1 _ ) (Sequent (l,r)) = Just [Sequent (MS.insert t1 l, r)]
andL1 _ _ = Nothing

andL2 (And _  t2) (Sequent (l,r)) = Just [Sequent (MS.insert t2 l, r)]
andL2 _ _ = Nothing

orR1  (Or  t1 _ ) (Sequent (l,r)) = Just [Sequent (l, MS.insert t1 r)]
orR1 _ _ = Nothing

orR2  (Or  _  t2) (Sequent (l,r)) = Just [Sequent (l, MS.insert t2 r)]
orR2 _ _ = Nothing

impR  (Imp t1 t2) (Sequent (l,r)) = Just [Sequent (MS.insert t1 l, MS.insert t2 r)]
impR _ _ = Nothing

notL  (Not    t1) (Sequent (l,r)) = Just [Sequent (l, MS.insert t1 r)]
notL _ _ = Nothing

notR  (Not    t1) (Sequent (l,r)) = Just [Sequent (MS.insert t1 l, r)]
notR _ _ = Nothing

andR, orL, impL :: Term -> Sequent Term -> Sequent Term -> Maybe [Sequent Term]

andR  (And t1 t2) (Sequent (l1,r1)) (Sequent (l2,r2)) = Just [Sequent (l1, MS.insert t1 r1), Sequent (l2, MS.insert t2 r2)]
andR  _ _ _ = Nothing

orL   (Or  t1 t2) (Sequent (l1,r1)) (Sequent (l2,r2)) = Just [Sequent (MS.insert t1 l1, r1), Sequent (MS.insert t2 l2, r2)]
orL   _ _ _ = Nothing

impL  (Imp t1 t2) (Sequent (l1,r1)) (Sequent (l2,r2)) = Just [Sequent (l1, MS.insert t1 r1), Sequent (MS.insert t2 l2, r2)]
impL  _ _ _ = Nothing


steps :: [(String, InferRule Term)]
steps = [ ("I", StructureRule iden)
        , ("CL", FormulaRule contrL)
        , ("CR", FormulaRule contrR)
        , ("WL", FormulaRule weakL)
        , ("WR", FormulaRule weakR)
        , ("NL", FormulaRule $ leftTermSingle notL)
        , ("NR", FormulaRule $ rightTermSingle notR)
        , ("AL1", FormulaRule $ leftTermSingle andL1)
        , ("AL2", FormulaRule $ leftTermSingle andL2)
        , ("AR", FormulaeRule $ rightTermDouble andR)
        , ("OR1", FormulaRule $ rightTermSingle orR1)
        , ("OR2", FormulaRule $ rightTermSingle orR2)
        , ("OL", FormulaeRule $ leftTermDouble orL)
        , ("IR", FormulaRule $ rightTermSingle impR)
        , ("IL", FormulaeRule $ leftTermDouble impL)
        ]

-}

tmDAbs (Env (TypeEnvironment te)) (Expr (TmAbs v vt tm) t) | M.notMember v te = Just [(Env $ TypeEnvironment $ M.insert v t te, (Expr tm t))]
tmDAbs _ _ = Nothing

-- app (TypeEnvironment te) (Expr (TmApp tm1 tm2) t) = Just [(te, (Expr tm1 ()]
-- app _ _ = Nothing

termDestruction :: (TypingExpr -> TypingExpr -> Maybe [(TypingExpr, TypingExpr)]) -> Sequent TypingExpr -> Maybe [Sequent TypingExpr]
termDestruction f (Sequent (l,r)) | MS.null l = termDestruction f $ Sequent (MS.insert (Env (TypeEnvironment M.empty)) l,r)
                                  | otherwise = fmap (map (\(te,t)->Sequent (MS.singleton te, MS.singleton t))) $ f l' r'
                                  where
                                    l' = head $ MS.toList l
                                    r' = head $ MS.toList r


typingSteps :: [(String, InferRule TypingExpr)]
typingSteps = [ ("I", StructureRule iden), ("ABS", StructureRule $ termDestruction tmDAbs) ]
