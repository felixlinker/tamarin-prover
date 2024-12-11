{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Main.ScratchPad
  ( weakenNode
  , weakenEdge
  , steps
  , paths
  , methodsAt
  , getDebugInput
  , debug
  ) where

import qualified Data.Label as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace
import Main.REPL
import Theory

import Control.Monad.Reader (ReaderT (runReaderT))

{- This module meant for playing around with the Tamarin interactive proving
   REPL that can be found in @Main.REPL@. Before you make any changes to this
   file, we suggest running:
    git update-index --assume-unchanged src/Main/ScratchPad.hs

   This command ensures that any changed you make will not be tracked by git.
   You can undo this by running:
    git update-index --no-assume-unchanged src/Main/ScratchPad.hs

   Below is an example how to use the scratchpad. We load the minimal loop
   theory, access one of its lemma, and apply simplify. The @debugInput@
   defines the input to the printing function @debugM@, which prints results to
   the console.
-}

thy :: IO ClosedTheory
thy = loadThy "examples/features/cyclic/nested-loop.spthy"

steps :: REPL REPLProof
steps = getProofForLemma "FreshSeedInstantiate"
  >>= trace "--- starting constraint solving ---"
      stepAt 0 (solve 0) -- simplify
  >>= stepAt 0 (solve 0)
  >>= stepAt 1 (solve 0)
  >>= stepAt 1 (weakenNode "#t")
  >>= stepAt 1 (solve 0)

paths :: REPL REPLProof -> IO ()
paths = showPaths thy

methodsAt :: Int -> REPL REPLProof -> IO ()
methodsAt = showMethodsAt thy

debug :: IO ()
debug = showWith thy debugM debugInput

{- Executing @paths steps@ in GHCI will show a visual representation of the
   proof tree after applying the steps specified in @steps@. The paths in the
   tree will be indexed.

  Executing @methodsAt X steps@ will show the available proof methods at the
  path indexed with X. Using the outputs of @paths@ and @methodsAt@ can help
  find the indices required to apply more @solve@ steps in @steps@.
-}

type DebugInput = (ProofContext, MaudeHandle, REPLProof, NE.NonEmpty System)

-- | Execute the constraint solving steps defined above, and provide input to
--   debug monad @debugM@ defined below. The returned values will be provided as
--   arguments to @debugM@.
debugInput :: REPL DebugInput
debugInput = do
  prf <- steps
  let ctxt = rpCtxt prf
  let hnd = L.get pcMaudeHandle ctxt
  syss <- systemsAt 0 prf
  return (ctxt, hnd, prf, syss)

getDebugInput :: IO DebugInput
getDebugInput = thy >>= runReaderT debugInput

-- | Use the values returned above to perform debugging.
debugM :: DebugInput -> IO ()
debugM _ = do
  putStrLn "debugging..."
