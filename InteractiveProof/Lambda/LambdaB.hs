{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

module InteractiveProof.Lambda.LambdaB (Term (..), Context (..), steps, freeVars, vars, boundedVars, holePos, parseTerm, idValue) where

import InteractiveProof
import InteractiveProof.Lambda
import InteractiveProof.ProofTree
import Data.List

import Control.Lens hiding (Context)
import Control.Monad
-- import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((*>),(<*))

import Text.Parsec

data Term = Var Variable
          | Lam Variable Term
          | App Term Term
          deriving (Read, Eq, Ord)

data Context = Hole
             | CVar Variable
             | CLam Variable Context
             | CApp Context Context
             deriving (Read, Eq, Ord)

instance Statement Term

instance LambdaTerm Term where
    parseLambda = parse parseTerm "LambdaTerm"
    var = Var
    subst = substTerm
    alpha = alphaTerm

instance LambdaContext Term Context where
    split = splitTerm
    toContext = termToContext
    makeHole = makeTermHole
    patchHole = patchTermHole

instance LocativeTree Term where
    walk = walkTerm
    match = matchTerm
    subtree = subTerm

instance LocativeTree Context where
    walk = walkContext
    match = matchContext
    subtree = subContext

instance Formattable Term (TextFormat String) where
    toFormat x = TextFormat $ "(" ++ termToStr x ++ ")"
    parseFormat = parseTerm

instance Formattable Context (TextFormat String) where
    toFormat x = TextFormat $ "(" ++ contextToStr x ++ ")"
    parseFormat = parseContext

instance Show Term where
    show x =  "(" ++ termToStr x ++ ")"

instance Show Context where
    show x =  "(" ++ contextToStr x ++ ")"


parseTerm :: Stream b m Char => ParsecT b u m Term
parseTerm = pTerm
    where
      pVar = liftM Var $ many1 parseIdChar
      pLambda = do
        (string "^" <|> string "λ") <* spaces
        v <- many1 parseIdChar <* spaces
        string "." <* spaces
        t <- pTerm
        return $ Lam v t
      pTerm = do
        t1 <- pAtom
        t2 <- many $ spaces *> pAtom
        return $ unfoldApp t1 $ reverse t2
      unfoldApp x [] = x
      unfoldApp x [y] = App x y
      unfoldApp x (y:ys) = App (unfoldApp x ys) y
      pAtom = (string "(" >> pTerm <* string ")") <|> pLambda <|> pVar

parseContext :: Stream b m Char => ParsecT b u m Context
parseContext = pTerm
    where
      pHole = (string "_" <* spaces) >> return Hole
      pVar = liftM CVar $ many1 parseIdChar
      pLambda = do
        (string "^" <|> string "λ") <* spaces
        v <- many1 parseIdChar <* spaces
        string "." <* spaces
        t <- pTerm
        return $ CLam v t
      pTerm = do
        t1 <- pAtom
        t2 <- many $ spaces *> pAtom
        return $ unfoldApp t1 $ reverse t2
      unfoldApp x [] = x
      unfoldApp x [y] = CApp x y
      unfoldApp x (y:ys) = CApp (unfoldApp x ys) y
      pAtom = (string "(" >> pTerm <* string ")") <|> pLambda <|> pHole <|> pVar

termToStr :: Term -> String
termToStr (Var v)     = v
termToStr (Lam v t)     = "λ" ++ v ++ ". " ++ termToStr t
termToStr (App t1@(Lam _ _) t2@(App _ _))     = paren (termToStr t1) ++ " " ++ paren (termToStr t2)
termToStr (App t1@(Lam _ _) t2)     = paren (termToStr t1) ++ " " ++ termToStr t2
termToStr (App t1 t2@(App _ _))     = termToStr t1 ++ " " ++ paren (termToStr t2)
termToStr (App t1 t2)     = termToStr t1 ++ " " ++ termToStr t2

contextToStr :: Context -> String
contextToStr Hole     = "_"
contextToStr (CVar v)     = v
contextToStr (CLam v t)     = "λ" ++ v ++ ". " ++ contextToStr t
contextToStr (CApp t1@(CLam _ _) t2@(CApp _ _))     = paren (contextToStr t1) ++ " " ++ paren (contextToStr t2)
contextToStr (CApp t1@(CLam _ _) t2)     = paren (contextToStr t1) ++ " " ++ contextToStr t2
contextToStr (CApp t1 t2@(CApp _ _))     = contextToStr t1 ++ " " ++ paren (contextToStr t2)
contextToStr (CApp t1 t2)     = contextToStr t1 ++ " " ++ contextToStr t2

walkTerm :: (Term -> Maybe Term -> Term) -> Term -> Term
walkTerm f t@(Var _)     = f t Nothing
walkTerm f t@(Lam v t')   = f t (Just $ Lam v (walk f t'))
walkTerm f t@(App t1' t2') = f t (Just $ App (walk f t1') (walk f t2'))

matchTerm :: (Term -> Bool) -> Term -> [Pos]
matchTerm f = g
  where
    g t@(Var _) = f' t
    g t@(Lam _ t') = (f' t ++) $ fmap (0:) $ g t'
    g t@(App t1' t2') = (f' t ++) $ fmap (0:) (g t1') ++ fmap (1:) (g t2')

    f' t = [[] | f t]

walkContext :: (Context -> Maybe Context -> Context) -> Context -> Context
walkContext f t@Hole         = f t Nothing
walkContext f t@(CVar _)       = f t Nothing
walkContext f t@(CLam v t')    = f t (Just $ CLam v (walk f t'))
walkContext f t@(CApp t1' t2') = f t (Just $ CApp (walk f t1') (walk f t2'))

matchContext :: (Context -> Bool) -> Context -> [Pos]
matchContext f = g
  where
    g t@Hole = f' t
    g t@(CVar _) = f' t
    g t@(CLam _ t') = (f' t ++) $ fmap (0:) $ g t'
    g t@(CApp t1' t2') = (f' t ++) $ fmap (0:) (g t1') ++ fmap (1:) (g t2')

    f' t = [[] | f t]

freeVars :: Term -> [Variable]
freeVars (Var v) = [v]
freeVars (Lam v t) = delete v $ freeVars t
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2

vars :: Term -> [Variable]
vars (Var v) = [v]
vars (Lam v t) = [v] `union` freeVars t
vars (App t1 t2) = freeVars t1 `union` freeVars t2

boundedVars :: Context -> [[Variable]]
boundedVars Hole = [[]]
boundedVars (CVar _) = []
boundedVars (CLam v t) = fmap (union [v]) $ boundedVars t
boundedVars (CApp t1 t2) = boundedVars t1 ++ boundedVars t2

alphaTerm :: Variable -> Variable -> Term -> Term
alphaTerm vf vt = walk f
    where
      f (Var v)   _         = Var (if v == vf then vt else v)
      f (Lam v t) _         = Lam v (if v == vf then t else walk f t)
      f _         (Just t') = t'

substTerm :: Variable -> Term -> Term -> Term
substTerm vf t = walk f
    where
      f (Var v)   _         = if v == vf then t else Var v
      f _         (Just t') = t'

subTerm :: Term -> Pos -> Maybe Term
subTerm t [] = Just t
subTerm (Var _)     _     = Nothing
subTerm (Lam _ t)  (_:ps) = subTerm t  ps
subTerm (App t1 _) (0:ps) = subTerm t1 ps
subTerm (App _ t2) (1:ps) = subTerm t2 ps

subContext :: Context -> Pos -> Maybe Context
subContext t [] = Just t
subContext Hole         _     = Nothing
subContext (CVar _)     _     = Nothing
subContext (CLam _ t)  (_:ps) = subContext t  ps
subContext (CApp t1 _) (0:ps) = subContext t1 ps
subContext (CApp _ t2) (1:ps) = subContext t2 ps

termToContext :: Term -> Context
termToContext (Var v) = CVar v
termToContext (Lam v t) = CLam v (termToContext t)
termToContext (App t1 t2) = CApp (termToContext t1) (termToContext t2)

makeTermHole :: Term -> Pos -> Maybe Context
makeTermHole _ [] = Just Hole
makeTermHole (Var _)      _     = Nothing
makeTermHole (Lam v t)   (_:ps) = makeHole t ps >>= \c -> Just $ CLam v c
makeTermHole (App t1 t2) (0:ps) = makeHole t1 ps >>= \c -> Just $ CApp c (toContext t2)
makeTermHole (App t1 t2) (1:ps) = makeHole t2 ps >>= \c -> Just $ CApp (toContext t1) c

splitTerm :: Term -> Pos -> Maybe (Context, Term)
splitTerm t p = do
    c <- makeHole t p
    t' <- subtree t p
    return (c, t')

holePos :: Context -> [Pos]
holePos Hole = [[]]
holePos (CVar _) = []
holePos (CLam _ t) = fmap (0:) $ holePos t
holePos (CApp t1 t2) = fmap (0:) (holePos t1) ++ fmap (1:) (holePos t2)

patchTermHole :: Context -> Term -> Term
patchTermHole Hole tp = tp
patchTermHole (CVar v) _ = Var v
patchTermHole (CLam v t) tp = Lam v (patchHole t tp)
patchTermHole (CApp t1 t2) tp = App (patchHole t1 tp) (patchHole t2 tp)

betaStep :: Term -> Maybe Term
betaStep (App (Lam v t1) t2) = Just $ substTerm v t2 t1
betaStep _ = Nothing

etaStep :: Term -> Maybe Term
etaStep (Lam v (App t (Var v'))) | v == v' && v `notElem` freeVars t = Just t
etaStep _ = Nothing

idValue :: Term -> Maybe Term
idValue (App _ _) = Nothing
idValue t = Just t

steps :: [(String, ReductionStep Term)]
steps = map (_2 %~ ReductionStep) [("beta", betaStep), ("eta", etaStep)]

