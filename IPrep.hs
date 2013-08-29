{-# LANGUAGE MultiParamTypeClasses, Rank2Types, ImpredicativeTypes,
  FlexibleContexts, ScopedTypeVariables, FlexibleInstances #-}

module IPrep where
-- import Control.Arrow
-- import Control.Monad
import Control.Applicative ((<$>),(*>),(<*),pure)
import InteractiveProof
import InteractiveProof.Formula
import qualified InteractiveProof.Formula.ClassicPrep as FCP
import InteractiveProof.ProofTree
import Data.List
import Data.Maybe
import Control.Monad
-- import Control.Lens
import System.Console.Haskeline


import Text.Parsec
import Text.Parsec.String

type FormulaProofObj a = (ProofTree (Sequent a, ApplicableRule a))

data Prompt = Toplevel
            | Proving Int

data Proof = ClassicPrepProof (String, FormulaProofObj FCP.Term)

data Calculus = ClassicPrep [(String, InferRule FCP.Term)]

data Term = ClassicPrepTerm FCP.Term

instance Formattable Proof (TextFormat String) where
    toFormat po@(ClassicPrepProof (thm, p)) = TextFormat $ case toFormat p of
                                                             TextFormat str -> "thm:" ++ getProofFullName po ++ "\n" ++ str

instance Formattable Proof (TexFormat String) where
    toFormat po@(ClassicPrepProof (thm, p)) = TexFormat $ case toFormat p of
                                                            TexFormat str -> "\\begin{theorem}[" ++ getProofFullName po ++ "]\n\\begin{proof}\n" ++ str ++ "\n\\end{proof}\n\\end{theorem}"

getProofFullName :: Proof -> String
getProofFullName p = getCalcName p ++ ":" ++ getProofName p

getCalcName :: Proof -> String
getCalcName (ClassicPrepProof _) = "cp"

getProofName :: Proof -> String
getProofName (ClassicPrepProof (thm, _)) = thm
-- instance Formattable Proof (TexFormat String) where
--     toFormat (ClassicPrepProof thm p) = TexFormat $ case toFormat p of
--                                                       TexFormat str -> "thm:cp:" ++ thm ++ "\n" ++ str
--    parseFormat = parseFinchTree

calculi :: [(String, Calculus)]
calculi = [("cp", ClassicPrep FCP.steps)]

data Command a b c = Abort
                   | Help
                   | Command a
                   | Extract b c String
                   | Info
-- import Text.Parsec.String

-- newtype Variable = Variable String
--           deriving (Show, Eq, Ord, Read)

-- pTree :: (Show a, Statement a, Rule a (Redex a), LambdaContext a c)=> [(String, ReductionStep a)] -> a -> IO (Maybe (Tree (a, Redex a)))
pTree :: (Functor m, Monad m, Formattable a (TextFormat String), Formattable a (TexFormat String), Formula a, Ord a) => [(String, InferRule a)] -> (String -> m ()) -> (Prompt -> m String) -> Sequent a -> m (Maybe (ProofTree (Sequent a, ApplicableRule a)))
pTree steps putLn getLn = makeTree putLn ask rules
  where
    rules _ = []
    ask t cs = do
      putLn $ toFormat t
      ans <- parseLine putLn (getLn (Proving 0)) "tactic" $ pFail <|> pHelp <|> liftM Command (parseStep t steps)
      case ans of
        Abort -> return Nothing
        Help -> printHelp >> ask t cs
        Command r -> if applicableRule r t then return $ Just r else putLn "inapplicative" >> ask t cs
    pFail = string "fail" >> return Abort
    pHelp = string "help" >> return Help
    printHelp = putLn $ intercalate ", " $ map usageStr steps
    usageStr (n, StructureRule _) = n
    usageStr (n, VariableRule _) = n ++ " vs.."
    usageStr (n, FormulaRule _) = n ++ "(t)"
    usageStr (n, FormulaeRule _) = n ++ "(t)[l..][r..]"

loop :: (Functor m, Monad m) => (String -> m ()) -> (Prompt -> m String) -> [Proof] -> m [Proof]
loop putLn getLn proofs = do
    command <- getLn Toplevel
    case parse parseCommand "top level" command of
      Left err -> putLn (show err) >> loop putLn getLn proofs
      Right Abort -> return proofs
      Right Help -> printHelp >> loop putLn getLn proofs
      Right (Command c) -> proofCommandAndLoop c
      Right (Extract format calc thm) -> case find (\p -> getProofFullName p == calc ++ ":" ++ thm) proofs of
                                           Nothing -> putLn ("Theorem " ++ thm ++ " is not found.") >> loop putLn getLn proofs
                                           Just p -> putLn (extractString format p) >> loop putLn getLn proofs
      Right Info -> infoCommand proofs >> loop putLn getLn proofs
  where
--    proof :: (Functor m, Monad m) => [(String, InferRule a)] -> a -> m (Maybe (FormulaProofObj a))
    proof calc term = do
      tr <- pTree calc putLn getLn (singleton term)
      case tr of
        Nothing -> putLn "Proof failed." >> return tr
  --      Just p -> maybe (return ()) putStrLn $ cast (toFormat p :: TextFormat String)
        Just p -> putLn "Proof completed." >> return tr
    parseCommand :: (Stream s m Char)=> ParsecT s u m (Command (Calculus, String, Term) String String)
    parseCommand = do
      command <- spaces *> many1 letter <* spaces
      case lookup command commands of
        Nothing -> unexpected $ "command name: " ++ command
        Just p -> p
    commands :: (Stream s m Char)=> [(String, ParsecT s u m (Command (Calculus, String, Term) String String))]
    commands = [("exit", return Abort), ("help", return Help), ("thm", parseTheorem), ("theorem", parseTheorem), ("extract", parseExtract), ("info", return Info)]
    parseTheorem :: (Stream s m Char)=> ParsecT s u m (Command (Calculus, String, Term) a b)
    parseTheorem = fmap Command $ do
      calcName <- many1 letter <* spaces
      string ":"
      thmName <- many1 letter <* spaces <* string ":" <* spaces
      case lookup calcName calculi of
        Nothing -> unexpected $ "calculus name: " ++ calcName
        Just (ClassicPrep steps) -> parseCp steps thmName
    parseCp calc thm = do
      term <- parseFormula
      return (ClassicPrep calc, thm, ClassicPrepTerm term)
    parseExtract :: (Stream s m Char)=> ParsecT s u m (Command a String String)
    parseExtract = do
      string ":"
      format <- many1 letter <* spaces
      calcName <- many1 letter <* spaces
      string ":"
      thmName <- many1 letter <* spaces
      return $ Extract format calcName thmName
    printHelp = putLn "help, exit, theorem:<type> <name>:<theorem>, extract:<type> <name>, info"
    proofCommandAndLoop (ClassicPrep calc, thm, ClassicPrepTerm term) = proof calc term >>= (loop putLn getLn . maybe proofs (\p -> ClassicPrepProof (thm, p) : proofs))
--    infoCommand :: [Proof] -> m ()
    infoCommand proofs = forM_ names putLn
                    where
                      names = map (("thm:"++) . getProofFullName) proofs
    extractString :: (Formattable a (TextFormat String), Formattable a (TexFormat String), Formattable a String) => String -> a -> String
    extractString format p = case format of
                          "text" -> toFormat p
                          "tex" -> toString (toFormat p :: TexFormat String)
                          _ -> "format not found."

main :: IO ()
main = runInputT haskelineSettings (void $ loop putLn getLn [])
    where 
      putLn = outputStrLn
      promptStr Toplevel = "% "
      promptStr (Proving n) = show n ++ "> "
      getLn pstr =  do
        minput <- getInputLine $ promptStr pstr
        case minput of
          Nothing -> getLn pstr
          Just input -> return input

      haskelineSettings = Settings {
                 complete = completeFilename,
                 historyFile = Just ".ilhist",
                 autoAddHistory = True
                 }
