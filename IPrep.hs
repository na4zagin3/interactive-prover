{-# LANGUAGE MultiParamTypeClasses, Rank2Types, ImpredicativeTypes,
  FlexibleContexts, ScopedTypeVariables, FlexibleInstances #-}

module IPrep where
-- import Control.Arrow
-- import Control.Monad
--import Control.Applicative ((<$>),(*>),(<*),pure)
import Control.Applicative ((*>),(<*))
import InteractiveProof
import InteractiveProof.Formula
import qualified InteractiveProof.Formula.ClassicPrep as FCP
import InteractiveProof.ProofTree
import Data.Monoid
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Control.Lens()
import System.Console.Haskeline
import System.Environment


import Text.Parsec hiding (State)
import Text.Parsec.String()

type FormulaProofObj a = (AnnotatedProofTree (Sequent a, ApplicableRule a))

data Prompt = Toplevel
            | Proving Int

data File = File [Section]

data Section = Section String [Proof]

data Proof = ClassicPrepProof (String, FormulaProofObj FCP.Term)

data Calculus = ClassicPrep [(String, InferRule FCP.Term)]

data Term = ClassicPrepTerm FCP.Term

data Environment m = Environment { putLn :: String -> m ()
                                 , getLn :: Prompt -> m String
                                 , inputWithFile :: forall a. FilePath -> Environment m -> (Environment m -> m a) -> m a
--                                 , outputWithFile :: forall a. FilePath -> Environment m -> (Environment m -> m a) -> m a
                                 }

-- wfm :: FilePath -> (StateT [String] m b) -> m b
-- wfm' :: FilePath -> (StateT [String] (StateT [String] m b) b) -> (StateT [String] m b) b

instance Formattable Section (TextFormat String) where
    toFormat (Section name ps) = (TextFormat ("Section " ++ name ++ "\n") `mappend`) $ mconcat $ map (\p-> TextFormat "\n" `mappend` toFormat p) ps
    parseFormat = undefined

instance Formattable File (TextFormat String) where
    toFormat (File ss) = mconcat $ map toFormat ss
    parseFormat = undefined

instance Formattable Section (TexFormat String) where
    toFormat (Section name ps) = (TexFormat ("\\section{" ++ name ++ "}\n") `mappend`) $ mconcat $ map (\p-> TexFormat "\n" `mappend` toFormat p) ps
    parseFormat = undefined

instance Formattable File (TexFormat String) where
    toFormat (File ss) = texOutput ss
    parseFormat = undefined

texOutput :: [Section] -> TexFormat String
texOutput ss = (preamble `mappend` contents) `mappend` footer
    where
      preamble :: TexFormat String
      preamble = mconcat $ [ TexFormat "\\documentclass[a4paper]{article}\n"
                           , TexFormat "\\usepackage{amsmath,amsthm}\n"
                           , TexFormat "\\usepackage{etex}\n"
                           , TexFormat "\\usepackage{bussproofs}\n"
                           , TexFormat "\\theoremstyle{definition}\n"
                           , TexFormat "\\newtheorem{theorem}{Theorem}\n"
                           , TexFormat "\\begin{document}\n"
                           ]
      contents :: TexFormat String
      contents = mconcat $ map toFormat ss
      footer :: TexFormat String
      footer   = mconcat $ [ TexFormat "\\end{document}"
                           ]

instance Formattable Proof (TextFormat String) where
    toFormat po@(ClassicPrepProof (_, p)) = TextFormat $ case toFormat p of
                                                             TextFormat str -> "thm:" ++ getProofFullName po ++ "\n" ++ str
    parseFormat = undefined

instance Formattable Proof (TexFormat String) where
    toFormat po@(ClassicPrepProof (_, p)) = mconcat [ header, toFormat p, footer]
        where
          header = return $ "\\begin{theorem}[" ++ getProofFullName po ++ "]\n\\begin{prooftree}\n"
          footer = return $ "\n\\end{prooftree}\n\\end{theorem}"
    parseFormat = undefined

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
                   | EmptyLine
                   | Command a
                   | Extract b c String
                   | Info
                   | ReadFile FilePath
-- import Text.Parsec.String

-- newtype Variable = Variable String
--           deriving (Show, Eq, Ord, Read)

-- pTree :: (Show a, Statement a, Rule a (Redex a), LambdaContext a c)=> [(String, ReductionStep a)] -> a -> IO (Maybe (Tree (a, Redex a)))
-- m (Maybe (ProofTree (b, c)))
-- m (Maybe (AnnotProofTree (b, c)))
pTree :: (Functor m, Monad m, Formattable a (TextFormat String), Formattable a (TexFormat String), Formula a, Ord a) => [(String, InferRule a)] -> Environment m -> Sequent a -> m (Maybe (FormulaProofObj a))
pTree steps env = fmap (liftM (liftM AnnotatedProofTree)) $ makeTree envPutLn ask rules
  where
    rules _ = []
    ask n t cs = do
      envPutLn . toString $ (toFormat t :: TextFormat String)
      ans <- parseLineM envPutLn (envGetLn (Proving n)) "tactic" TextFormat $ spaces >> (pFail <|> pHelp <|> liftM Command (parseStep t steps))
      case ans of
        Abort -> return Nothing
        Help -> printHelp >> ask n t cs
        Command r -> if applicableRule r t then return $ Just r else envPutLn "inapplicative" >> ask n t cs
    pFail = try (string "fail" <|> string "abort" ) >> return Abort
    pHelp = try (string "help") >> return Help
    printHelp = envPutLn $ intercalate ", " $ map usageStr steps
    usageStr (n, StructureRule _) = n
    usageStr (n, VariableRule _) = n ++ " vs.."
    usageStr (n, FormulaRule _) = n ++ "(t)"
    usageStr (n, FormulaeRule _) = n ++ "(t)[l..][r..]"
    envPutLn = putLn env
    envGetLn = getLn env

loop :: (Functor m, Monad m) => Environment m -> [Proof] -> m [Proof]
loop env proofs = do
    command <- envGetLn Toplevel
    case parse parseCommand "top level" command of
      Left err -> envPutLn (show err) >> loop env proofs
      Right Abort -> return proofs
      Right Help -> printHelp >> loop env proofs
      Right EmptyLine -> loop env proofs
      Right (Command c) -> proofCommandAndLoop c
      Right (Extract format calc thm) -> case find (\p -> getProofFullName p == calc ++ ":" ++ thm) proofs of
                                           Nothing -> envPutLn ("Theorem " ++ thm ++ " is not found.") >> loop env proofs
                                           Just p -> envPutLn (extractString format p) >> loop env proofs
      Right Info -> infoCommand proofs >> loop env proofs
      Right (ReadFile path) -> envPutLn ("Read: " ++ path) >> (inputWithFile env) path env (flip loop proofs) >>= loop env
  where
--    proof :: (Functor m, Monad m) => [(String, InferRule a)] -> a -> m (Maybe (FormulaProofObj a))
    proof calc term = do
      tr <- pTree calc env (singleton term)
      case tr of
        Nothing -> envPutLn "Proof failed." >> return tr
  --      Just p -> maybe (return ()) putStrLn $ cast (toFormat p :: TextFormat String)
        Just _ -> envPutLn "Proof completed." >> return tr
    parseCommand :: (Stream s m Char)=> ParsecT s u m (Command (Calculus, String, Term) String String)
    parseCommand = do
      command <- spaces *> many letter <* spaces
      fromMaybe (unexpected $ "command name: " ++ command) $ lookup command commands
    commands :: (Stream s m Char)=> [(String, ParsecT s u m (Command (Calculus, String, Term) String String))]
    commands = [("", return EmptyLine), ("qed", return EmptyLine), ("abort", return Abort), ("exit", return Abort), ("help", return Help), ("thm", parseTheorem), ("theorem", parseTheorem), ("extract", parseExtract), ("info", return Info), ("source", parseReadFile)]
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
    parseReadFile :: (Stream s m Char)=> ParsecT s u m (Command a String String)
    parseReadFile = do
      path <- spaces *> stringLiteral <|> many1 (noneOf " \t\n\"")
      return $ ReadFile path
    printHelp = envPutLn "help, exit, theorem:<type> <name>:<theorem>, extract:<type> <name>, info, source <file>"
    proofCommandAndLoop (ClassicPrep calc, thm, ClassicPrepTerm term) = proof calc term >>= (loop env . maybe proofs (\p -> ClassicPrepProof (thm, p) : proofs))
--    infoCommand :: [Proof] -> m ()
    infoCommand proofs' = forM_ names envPutLn
                    where
                      names = map (("thm:"++) . getProofFullName) proofs'
    extractString :: (Formattable a (TextFormat String), Formattable a (TexFormat String)) => String -> a -> String
    extractString format p = case format of
                          "text" -> toString (toFormat p :: TexFormat String)
                          "tex" -> toString (toFormat p :: TexFormat String)
                          _ -> "format not found."
    envPutLn = putLn env
    envGetLn = getLn env
    escapeOrStringChar :: (Stream s m Char)=> ParsecT s u m Char
    escapeOrStringChar = try (string "\\" >> ((string "\\" >> return '\\') <|> (string "\"" >> return '"'))) <|> anyChar
    stringLiteral :: (Stream s m Char)=> ParsecT s u m String
    stringLiteral = do
      char '"'
      str <- many1 escapeOrStringChar
      char '"' <?> "end of string"
      return str

main :: IO ()
main = do
    args <- getArgs
    let mpath = case args of
                  [] -> Nothing
                  [path] -> Just path
    prover mpath

prover :: Maybe FilePath -> IO ()
prover mpath = do
      proofs <- runInputTBehaviorWithPrefs haskelineBehavior defaultPrefs haskelineSettings (loop hlineEnv [])
      case mpath of
        Nothing -> return ()
        Just path -> writeFile path $ toString $ (toFormat (File [Section "main" $ reverse proofs]) :: TexFormat String)
    where 
      hlineEnv = Environment { putLn = putLn', getLn = getLn', inputWithFile = envWithFile' }
      putLn' = outputStrLn
      promptStr Toplevel = "% "
      promptStr (Proving n) = show n ++ "> "
      getLn' pstr =  do
        minput <- getInputLine $ promptStr pstr
        case minput of
          Nothing -> getLn' pstr
          Just input -> return input
--      envWithFile' :: (MonadException m) => FilePath -> Environment (InputT m) -> (Environment (InputT m) -> InputT m a) -> InputT m a
      envWithFile' path env f = lift $ runInputTBehavior (useFile path) haskelineSettings (f (Environment { putLn = putLn env, getLn = \_ -> liftM (maybe "abort" id) $ getInputLine "", inputWithFile = inputWithFile env }))


haskelineSettings :: (MonadIO m) =>Settings m
haskelineSettings = Settings {
           complete = completeFilename,
           historyFile = Just ".ilhist",
           autoAddHistory = True
           }

haskelineBehavior :: Behavior
haskelineBehavior = defaultBehavior

pop :: (Monad m)=> StateT [a] m (Maybe a)
pop = do
    l <- get
    if null l
      then return Nothing
      else do
        put $ tail l
        return . Just $ head l
