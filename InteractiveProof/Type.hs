{-# LANGUAGE FlexibleContexts #-}
module InteractiveProof.Type (Type, parseType) where

import Text.Parsec

class Type a where
    parseType :: Stream b m Char => ParsecT b u m a
