{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveDataTypeable #-}
module InteractiveProof where

import Prelude hiding (foldr, foldl)
import Data.Foldable (Foldable, foldr, foldl)
import Data.Typeable
import Data.Functor.Identity
import Text.Parsec
import Text.Parsec.String
import Control.Lens hiding (uncons)

type Variable = String

type RuleDialog a = a -> [String] -> IO Int

chooseRule :: (Formattable a String) => RuleDialog a
chooseRule t sps = do
    putStrLn $ toFormat t
    mapM_ (putStrLn . \(i,str) -> show i ++ ": " ++ str) $ zip [(0::Integer)..] sps
    fmap read getLine


paren :: String -> String
paren x = "(" ++ x ++ ")"

unfoldL :: (a -> a -> a) -> a -> [a] -> a
unfoldL c x ys = unfoldL' c x $ reverse ys

unfoldL' :: (a -> a -> a) -> a -> [a] -> a
unfoldL' _ x [] = x
unfoldL' c x [y] = c x y
unfoldL' c x (y:ys) = c (unfoldL' c x ys) y

unfoldR :: (a -> a -> a) -> a -> [a] -> a
unfoldR _ x [] = x
unfoldR c x [y] = c x y
unfoldR c x (y:ys) = c y (unfoldR c x ys)

parseLine :: (Functor m, Monad m)=>(String -> m ()) -> m String -> String -> Parser a -> m a
parseLine putLn getLn n p = do
    let f = fmap (parse p n) getLn >>= either (\x -> putLn (show x) >> f) return
    f

class Formattable a b where
    toFormat :: a -> b
    parseFormat :: Stream b m Char => ParsecT b u m a
    fromFormat :: Stream b Data.Functor.Identity.Identity Char => b -> Maybe a
    fromFormat s = either (const Nothing) Just $ parse parseFormat "formattable" s

instance Formattable String (TextFormat String) where
    toFormat = TextFormat . id
    fromFormat (TextFormat str) = Just str
    parseFormat = many anyChar

instance (Formattable a (TextFormat String))=> Formattable a String where
    toFormat x = case toFormat x of
                    (TextFormat str) -> str
    fromFormat = fromFormat . TextFormat
    parseFormat = undefined

instance Formattable (TexFormat String) (TextFormat String) where
    toFormat (TexFormat str) = TextFormat str
    fromFormat (TextFormat str) = Just $ TexFormat str
    parseFormat = undefined

newtype TexFormat a = TexFormat a
--    deriving (Typeable)
newtype TextFormat a = TextFormat a
--    deriving (Typeable)

instance (Stream s m t, Functor m) => Stream (TexFormat s) m t where
    uncons (TexFormat x) = fmap (fmap (_2 %~ TexFormat)) $ uncons x

instance (Stream s m t, Functor m) => Stream (TextFormat s) m t where
    uncons (TextFormat x) = fmap (fmap (_2 %~ TextFormat)) $ uncons x

instance (Typeable a) => Typeable (TextFormat a) where
    typeOf (TextFormat a) = typeOf a

instance (Typeable a) => Typeable (TexFormat a) where
    typeOf (TexFormat a) = typeOf a

instance Foldable TexFormat where
        foldr f z (TexFormat x) = f x z

        foldl f z (TexFormat x) = f z x
