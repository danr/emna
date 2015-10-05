{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
module Main where

import Tip.HaskellFrontend
import Tip.QuickSpec
import Tip.Core
import Tip.Fresh
import Tip.Passes
import Tip.Pretty
import Tip.Pretty.SMT as SMT

import Tip.Utils.Rename

import Data.List (sort, isInfixOf)

import qualified Data.Traversable as T

import Data.Unique

import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Process
import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Workers

import Text.PrettyPrint (Doc)

import System.Environment

import Waldmeister


main :: IO ()
main = do
  [file] <- getArgs
  loop waldmeister =<< exploreTheory =<< fmap (either error ren) (readHaskellOrTipFile file defaultParams)
  where
  ren = renameWith (\ x -> [ I i (varStr x) | i <- [0..] ])

data I = I Int String
  deriving (Eq,Ord,Show)

instance PrettyVar I where
   varStr (I x s) = s

instance Name I where
  fresh             = refresh (I undefined "x")
  refresh (I _ s)   = do u <- fresh; return (I u s)
  getUnique (I u _) = u

loop :: Name a => Prover -> Theory a -> IO ()
loop prover thy = go False conjs [] thy{ thy_asserts = assums }
  where
  (conjs,assums) = theoryGoals thy

  go _     []     [] _  = putStrLn "Finished!"
  go False []     _ _   = return ()
  go True  []     q thy = do putStrLn "Reconsidering conjectures..."
                             go False (reverse q) [] thy
  go b     (c:cs) q thy =
    do r <- tryProve prover c thy
       case r of
         True  -> go True cs q     thy{ thy_asserts = makeProved c:thy_asserts thy }
         False -> go b    cs (c:q) thy

makeProved :: Formula a -> Formula a
makeProved (Formula _ tvs b) = Formula Assert tvs b

formulaVars :: Formula a -> [Local a]
formulaVars = fst . forallView . fm_body

tryProve :: Name a => Prover -> Formula a -> Theory a -> IO Bool
tryProve prover fm thy =
  do let tree = freshPass (obligations fm) thy

     ptree :: Tree (Promise [Obligation Result]) <- T.traverse (promise prover) tree

     let timeout      = 1000 * 1000 -- microseconds
         processes    = 2

     workers (Just timeout) processes (interleave ptree)

     let (prenex,term) = forallView (renameWith (disambig varStr) (fm_body fm))

     putStrLn (ppRender term)

     (errs,res) <- evalTree (any (not . isSuccess) . map ob_content) ptree

     case res of
       Obligation (ObInduction coords _ n) _:_
         | sort (map (ind_num . ob_info) res) == [0..n-1]
         , all (isSuccess . ob_content) res
           -> do if null coords
                    then putStrLn $ "Proved without using induction"
                    else putStrLn $ "Proved by induction on " ++ unwords (map (lcl_name . (prenex !!)) coords)
                 sequence_ [ putStrLn s | Obligation _ (Success s) <- res, not (null s) ]

         | otherwise
           -> do putStrLn $ "Confusion :("
                 mapM_ print res

       _ -> putStrLn "Failed to prove."

     -- mapM_ print res

     sequence_
       [ case e of
           Obligation _ (Unknown (ProcessResult err out _)) -> putStrLn (err ++ "\n" ++ out)
           Obligation (ObInduction coords i _) Disproved ->
             do return ()
                -- putStrLn $ unwords (map (lcl_name . (prenex !!)) coords) ++ " " ++ show i ++ " disproved"
           _ -> print e
       | e <-  errs
       ]

     return (not (null res))

obligations :: Name a => Formula a -> Theory a -> Fresh (Tree (Obligation (Theory a)))
obligations fm thy0 =
  requireAny <$>
    sequence
      [ pack coords <$>
          runPass
            (Induction coords)
            (thy0 { thy_asserts = fm : thy_asserts thy0})
      | coords <- []:combine [ [i] | (_,i) <- formulaVars fm `zip` [0..] ]
      ]
  where
  combine xs = xs ++ [ ys ++ zs | ys <- xs, zs <- xs, ys /= zs ]
  pack coords thys =
    requireAll
      [ Leaf (Obligation (ObInduction coords i (length thys)) thy)
      | (thy,i) <- thys `zip` [0..]
      ]

data Obligation a = Obligation
    { ob_info     :: ObInfo
    , ob_content  :: a
    }
  deriving (Show,Functor,Foldable,Traversable)

data ObInfo
  = ObInduction
      { ind_coords  :: [Int]
      , ind_num     :: Int
      , ind_nums    :: Int
      -- , ind_skolems :: [v]
      -- , ind_terms   :: [Expr v]
      }
  deriving (Eq,Ord,Show)

data Result = Success String | Disproved | Unknown ProcessResult
  deriving (Eq,Ord,Show)

isUnknown :: Result -> Bool
isUnknown Unknown{} = True
isUnknown _         = False

isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess _         = False

data Prover = Prover
  { prover_cmd    :: String -> (String,[String])
  , prover_ext    :: String
  , prover_passes :: [StandardPass]
  , prover_pretty :: forall a . Name a => Theory a -> Doc
  , prover_pipe   :: ProcessResult -> Result
  }

promise :: Name a => Prover -> Obligation (Theory a) -> IO (Promise [Obligation Result])
promise Prover{..} (Obligation info thy) =
  do u <- newUnique
     let filename = "/tmp/" ++ show (hashUnique u) ++ prover_ext
     writeFile filename (show (prover_pretty (head (freshPass (runPasses prover_passes) thy))))
     let (prog,args) = prover_cmd filename
     promise <- processPromise prog args ""

     let update :: PromiseResult ProcessResult -> PromiseResult [Obligation Result]
         update Cancelled = Cancelled
         update Unfinished = Unfinished
         update (An pr) = An [Obligation info (prover_pipe pr)]

     return promise{ result = fmap update (result promise) }

z3 :: Prover
z3 = Prover
  { prover_cmd = \ filename -> ("z3",["-smt2",filename])
  , prover_ext = ".smt2"
  , prover_passes =
      [ TypeSkolemConjecture, Monomorphise False
      , LambdaLift, AxiomatizeLambdas
      , SimplifyGently, CollapseEqual, RemoveAliases
      , SimplifyGently, AxiomatizeFuncdefs2
      , SimplifyGently, Monomorphise False
      , SimplifyGently, NegateConjecture
      ]
  , prover_pretty = SMT.ppTheory
  , prover_pipe =
      \ pr@(ProcessResult err out exc) ->
          if "unsat" `isInfixOf` out
             then Success ""
             else Unknown pr
  }

waldmeister :: Prover
waldmeister = Prover
  { prover_cmd = \ filename -> ("waldmeister",[filename,"--auto"])
  , prover_ext = ".w"
  , prover_passes =
      [ TypeSkolemConjecture, Monomorphise False
      , LambdaLift, AxiomatizeLambdas, LetLift
      , SimplifyGently, CollapseEqual, RemoveAliases
      , SimplifyGently, AxiomatizeFuncdefs2, AxiomatizeDatadeclsUEQ
      , SimplifyGently, Monomorphise False
      , SkolemiseConjecture
      ]
  , prover_pretty = Waldmeister.ppTheory
  , prover_pipe =
      \ pr@(ProcessResult err out exc) ->
          if "Waldmeister states: Goal proved." `isInfixOf` out
             then Success (findProof out)
             else if "Waldmeister states: System completed." `isInfixOf` out
               then Disproved
               else Unknown pr
  }
  where
  findProof = unlines . map changeTheorem . drop 2 . dropWhile (/= "Proof:") . lines
  changeTheorem = removeBy . change [("Theorem 1","Case")]

  removeBy s | "by Axiom" `isInfixOf` s = " ="
  removeBy s = s

change :: Ord a => [([a],[a])] -> [a] -> [a]
change _   []        = []
change tbl xs@(y:ys) =
  case
    [ v ++ change tbl (drop (length k) xs)
    | (k,v) <- tbl
    , take (length k) xs == k
    ] of
    r:_ -> r
    []  -> y:change tbl ys


