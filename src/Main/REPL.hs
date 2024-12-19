{-# LANGUAGE ViewPatterns #-}
module Main.REPL
  ( REPL
  , REPLProof(..)
  , runREPL
  , loadThy
  , getProofForLemma
  , solve
  , weakenNode
  , weakenEdge
  , weakenLessAtom
  , weakenAGAt
  , stepAt
  , systemsAt
  , showMethodsAt
  , showPaths
  , showWith
  ) where

import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Data.Either (fromLeft)
import qualified Data.List.NonEmpty as NE
import qualified Data.Label as L
import qualified Data.Map as M
import qualified Data.Set as S
import Main.TheoryLoader as L (closeTheory, loadTheory, defaultTheoryLoadOptions, TheoryLoadError, TheoryLoadOptions(..))
import Theory
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Monad (guard, void)
import Text.PrettyPrint.Class (render)
import Utils.Misc (peak, (!?))
import Data.List.NonEmpty (NonEmpty)
import Theory.Text.Parser.Token (nodevar, edge, Parser, ParserState (PState))
import Text.Parsec (runParser)
import Data.List (find)

type REPL = ReaderT ClosedTheory IO

runREPL :: IO ClosedTheory -> REPL a -> IO a
runREPL thy repl = thy >>= runReaderT repl

maybeREPL :: String -> Maybe a -> REPL a
maybeREPL reason = maybe (fail reason) return

loadOptions :: TheoryLoadOptions
loadOptions = defaultTheoryLoadOptions { derivationChecks = 0 }

loadThy :: FilePath -> IO ClosedTheory
loadThy inFile = either (error . show) id <$> errOrThy
  where
    errOrThy :: IO (Either TheoryLoadError ClosedTheory)
    errOrThy = runExceptT $ do
      srcThy <- lift $ readFile inFile
      thy    <- fromLeft (error "diff theory") <$> loadTheory loadOptions srcThy inFile

      let sig = L.get thySignature thy
      sig'   <- lift $ toSignatureWithMaude loadOptions.maudePath sig

      fromLeft (error "diff theory") . snd <$> L.closeTheory "" loadOptions sig' (Left thy)

type PathMap = M.Map Int (ProofPath, [ProofMethod])

data REPLProof = REPLProof
  { rpProof :: IncrementalProof
  , rpCtxt  :: ProofContext
  , rpPaths :: PathMap }

rankMethods :: ProofContext -> NonEmpty System -> [ProofMethod]
rankMethods ctxt syss =
  let heuristic = fromMaybe (defaultHeuristic False) (L.get pcHeuristic ctxt)
      ranking = useHeuristic heuristic (length syss)
      tactic = fromMaybe [defaultTactic] (L.get pcTactic ctxt)
  in map fst $ rankProofMethods ranking tactic ctxt syss

collectPaths :: ProofContext -> IncrementalProof -> PathMap
collectPaths ctxt prf = M.fromList $ zip [0..] $ map (\p -> (p, getMethods p)) $ go prf
  where
    go :: IncrementalProof -> [ProofPath]
    go (LNode _ cs)
      | M.null cs = [[]]
      | otherwise = concatMap (\(ccn, t) -> map (ccn:) $ go t) $ M.toList cs

    getMethods :: ProofPath -> [ProofMethod]
    getMethods path = fromMaybe (error "illegal path") $ do
      (_, syss) <- prf `atPath` path
      return $ rankMethods ctxt syss

getProofForLemma :: String -> REPL REPLProof
getProofForLemma name = do
  thy <- ask
  let lem = peak $ mapMaybe (matcher thy) (L.get thyItems thy)
  maybeREPL "No such lemma" lem
  where
    matcher :: ClosedTheory -> TheoryItem ClosedProtoRule IncrementalProof () -> Maybe REPLProof
    matcher thy (LemmaItem l) = do
      guard (L.get lName l == name)
      let prf = L.get lProof l
      let ctxt = getProofContext l thy
      return $ REPLProof prf ctxt (collectPaths ctxt prf)
    matcher _ _               = Nothing

solve :: Int -> System -> [ProofMethod] -> Maybe ProofMethod
solve i _ ms = ms !? i

parseSimple :: Parser a -> String -> Maybe a
parseSimple p str = either (const Nothing) Just (runParser p (PState mempty S.empty) "" str)

weakenNode :: String -> a -> b -> Maybe ProofMethod
weakenNode n _ _ = SolveGoal . Weaken . WeakenNode <$> parseSimple nodevar n

weakenEdge :: String -> a -> b -> Maybe ProofMethod
weakenEdge e _ _ = SolveGoal . Weaken . WeakenEdge <$> parseSimple edge e

weakenLessAtom :: String -> String -> a -> b -> Maybe ProofMethod
weakenLessAtom n1 n2 _ _ =
  SolveGoal . Weaken <$> (WeakenLessAtom  <$> parseSimple nodevar n1
                                          <*> parseSimple nodevar n2)

weakenAGAt :: String -> System -> a -> Maybe ProofMethod
weakenAGAt nids s _ = do
  nid <- parseSimple nodevar nids
  ag <- find ((Just nid ==) . getAgNodeId) $ M.keys $ L.get sGoals s
  return $ SolveGoal $ Weaken $ WeakenGoal ag
  where
    getAgNodeId :: Goal -> Maybe NodeId
    getAgNodeId (ActionG n _) = Just n
    getAgNodeId _ = Nothing

stepAt :: Int -> (System -> [ProofMethod] -> Maybe ProofMethod) -> REPLProof -> REPL REPLProof
stepAt pathIdx fm prf =
  let mPath = M.lookup pathIdx $ rpPaths prf
      iPrf = rpProof prf
      ctxt = rpCtxt prf
  in do
  (path, methods) <- maybeREPL "illegal path index" mPath
  (_, syss) <- maybeREPL "illegal path" (iPrf `atPath` path)
  let method = fromMaybe (error "illegal method") $ fm (NE.head syss) methods
  iPrf' <- maybeREPL "applying method failed" $ modifyAtPath (runProver (oneStepProver method) ctxt (length syss)) [] path iPrf
  return (REPLProof iPrf' ctxt (collectPaths ctxt iPrf'))

systemsAt :: Int -> REPLProof -> REPL (NonEmpty System)
systemsAt pathIdx prf =
  let mPath = M.lookup pathIdx $ rpPaths prf
      iPrf = rpProof prf
  in do
    (path, _) <- maybeREPL "illegal path index" mPath
    (_, syss) <- maybeREPL "illegal path" (iPrf `atPath` path)
    return syss

getMethodsAt :: Int -> REPLProof -> REPL [ProofMethod]
getMethodsAt i prf = maybe (fail "illegal index") (return . snd) (M.lookup i $ rpPaths prf)

showMethodsAt :: IO ClosedTheory -> Int -> REPL REPLProof -> IO ()
showMethodsAt thy i m = do
  methods <- runREPL thy (m >>= getMethodsAt i)
  mapM_ printMethod (zip [0..] methods)
  where
    printMethod :: (Int, ProofMethod) -> IO ()
    printMethod (j, method) = putStrLn $ show j ++ ": " ++ render (prettyProofMethod method)

showPaths :: IO ClosedTheory -> REPL REPLProof -> IO ()
showPaths thy m = do
  prf <- runREPL thy m
  printTree $ rpProof prf

printTree :: IncrementalProof -> IO ()
printTree p = do
  _ <- go "" 0 "(root)" p
  putChar '\n'
  where
    go :: String -> Int -> CaseName -> IncrementalProof -> IO Int
    go prefix leafNo (showCn -> cn) (LNode _ cs)
      | M.null cs = do
        putStr $ '\n':prefix ++ cn ++ " (" ++ show leafNo ++ ")"
        return $ leafNo + 1
      | otherwise = do
        putStr $ '\n':prefix ++ cn
        let nextPrefix = map mapChar prefix ++ "+--"
        foldl (step nextPrefix) (return leafNo) (M.toList cs)

    step :: String -> IO Int -> (CaseName, IncrementalProof) -> IO Int
    step prefix mi (cn, prf) = do
      i <- mi
      go prefix i cn prf

    showCn :: CaseName -> String
    showCn "" = "(single case)"
    showCn cn = cn

    mapChar :: Char -> Char
    mapChar '+' = '|'
    mapChar '-' = ' '
    mapChar x   = x

showWith :: IO ClosedTheory -> (a -> IO b) -> REPL a -> IO ()
showWith thy cmd m = do
  repl <- runREPL thy m
  void $ cmd repl
