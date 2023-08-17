module Main.REPL
  ( loadThy
  , lemmas
  , systemAt
  , maudeHandle
  ) where

import Control.Monad.Except (runExceptT, MonadIO (liftIO))
import Data.Either (fromLeft)
import Data.Label
import qualified Data.Map as M
import qualified Data.Set as S
import Main.TheoryLoader as L (closeTheory, loadTheory, defaultTheoryLoadOptions, oMaudePath, TheoryLoadError)
import Theory
import Data.Maybe (mapMaybe, fromJust, fromMaybe)
import Theory.Constraint.Renaming
import Theory.Constraint.System

loadThy :: FilePath -> IO ClosedTheory
loadThy inFile = either (error . show) id <$> errOrThy
  where
    errOrThy :: IO (Either TheoryLoadError ClosedTheory)
    errOrThy = runExceptT $ do
      srcThy <- liftIO $ readFile inFile
      thy    <- fromLeft (error "diff theory") <$> loadTheory defaultTheoryLoadOptions srcThy inFile

      let sig = get thySignature thy
      sig'   <- liftIO $ toSignatureWithMaude (get oMaudePath defaultTheoryLoadOptions) sig

      fromLeft (error "diff theory"). snd <$> L.closeTheory "" defaultTheoryLoadOptions sig' (Left thy)

lemmas :: ClosedTheory -> [Lemma IncrementalProof]
lemmas = mapMaybe matcher . get thyItems
  where
    matcher :: TheoryItem ClosedProtoRule IncrementalProof () -> Maybe (Lemma IncrementalProof)
    matcher (LemmaItem l) = Just l
    matcher _             = Nothing

systemAt :: ProofPath -> Lemma IncrementalProof -> Maybe System
systemAt path lem =
  let p = get lProof lem
  in psInfo . root =<< rec p path
  where
    rec :: Proof (Maybe System) -> ProofPath -> Maybe (Proof (Maybe System))
    rec p = foldl (\mm k -> M.lookup k . children =<< mm) (Just p)

maudeHandle :: ClosedTheory -> MaudeHandle
maudeHandle =
    get sigmMaudeHandle
  . get thySignature

thy = loadThy "examples/loops/Minimal_HashChain_solved.spthy"
ls = lemmas <$> thy
p = (!! 6) <$> ls
ctxt = do
  l <- p
  getProofContext l <$> thy
cand :: IO System
cand = fromJust . systemAt ["", "Check", "Gen_Stop", "", "Check", "Gen_Step", "", ""] <$> p
candRoots = do
  c <- ctxt
  getLoopRoots c <$> cand
tgt = (!! 3) . get sCycleTargets <$> cand
tgtRoots = do
  c <- ctxt
  getLoopRoots c <$> tgt
ren = do
  c <- cand
  t <- tgt
  computeRenaming (t ~> c :: MaybeRenaming LNSubst) . maudeHandle <$> thy
rs = do
  c <- cand
  t <- tgt
  th <- thy
  return $ map (\mr -> computeRenaming mr (maudeHandle th)) $ allNodeRenamings c t
