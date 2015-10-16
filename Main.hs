{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
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
import Tip.Scope
import Tip.Pretty.SMT as SMT

import Tip.Utils.Rename

import Data.Generics.Geniplate

import Data.List (sort, isInfixOf)
import Data.Char

import qualified Data.Traversable as T

import Data.Unique

import Control.Monad

import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Process
import Control.Concurrent.STM.Promise.Tree hiding (Node)
import Control.Concurrent.STM.Promise.Workers

import Text.PrettyPrint (Doc)

import System.Environment

import Waldmeister

import System.Console.CmdArgs
import System.Process (readProcessWithExitCode)

import qualified Data.Map as M
import Data.Map (Map)

data Args =
  Args
    { file    :: String
    , explore :: Bool
    , indvars :: Int
    }
  deriving (Show,Data,Typeable)

defArgs :: Args
defArgs =
  Args
    { file    = ""    &= argPos 0 &= typFile
    , explore = False &= name "e" &= help "Explore theory"
    , indvars = 1     &= name "v" &= help "Number of variables to do induction on"
    }
  &= program "emna" &= summary "simple inductive prover with proof output"

main :: IO ()
main = do
  args@Args{..} <- cmdArgs defArgs
  x <- readHaskellOrTipFile file defaultParams
  case x of
    Left err  -> putStrLn err
    Right thy ->
      do loop args waldmeister =<<
           ((if explore then exploreTheory else return)
            (passes (ren thy)) )
  where
  ren = renameWith (\ x -> [ I i (varStr x) | i <- [0..] ])
  passes =
    head . freshPass
      (runPasses
        [ UncurryTheory
        , SimplifyAggressively
        ])

data I = I Int String
  deriving (Eq,Ord,Show)

instance PrettyVar I where
  varStr (I x s) = s

instance Name I where
  fresh             = refresh (I undefined "x")
  refresh (I _ s)   = do u <- fresh; return (I u s)
  freshNamed s      = refresh  (I 0 s)
  getUnique (I u _) = u

loop :: Name a => Args -> Prover -> Theory a -> IO ()
loop args prover thy = go False conjs [] thy{ thy_asserts = assums }
  where
  (conjs,assums) = theoryGoals thy

  go _     []     [] _  = putStrLn "Finished!"
  go False []     _ _   = return ()
  go True  []     q thy = do putStrLn "Reconsidering conjectures..."
                             go False (reverse q) [] thy
  go b     (c:cs) q thy =
    do r <- tryProve args prover c thy
       case r of
         True  -> go True cs q     thy{ thy_asserts = makeProved c:thy_asserts thy }
         False -> go b    cs (c:q) thy

makeProved :: Formula a -> Formula a
makeProved (Formula _ tvs b) = Formula Assert tvs b

formulaVars :: Formula a -> [Local a]
formulaVars = fst . forallView . fm_body

tryProve :: Name a => Args -> Prover -> Formula a -> Theory a -> IO Bool
tryProve args prover fm thy =
  do let tree = freshPass (obligations args fm) thy

     ptree :: Tree (Promise [Obligation Result]) <- T.traverse (promise prover) tree

     let timeout      = 1000 * 1000 -- microseconds
         processes    = 2

     workers (Just timeout) processes (interleave ptree)

     let (prenex,term) = forallView (renameWith (disambig varStr) (fm_body fm))

     -- putStrLn (ppRender term)
     putStrLn (ppTerm (toTerm term))

     (errs,res) <- evalTree (any (not . isSuccess) . map ob_content) ptree

     case res of
       Obligation (ObInduction coords _ n) _:_
         | sort (map (ind_num . ob_info) res) == [0..n-1]
         , all (isSuccess . ob_content) res
           -> do if null coords
                    then putStrLn $ "Proved without using induction"
                    else putStrLn $ "Proved by induction on " ++ unwords (map (lcl_name . (prenex !!)) coords)
                 sequence_
                   [ do pf <- parsePCL s
                        putStrLn pf
                   | Obligation _ (Success (Just s)) <- res
                   ]

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

obligations :: Name a => Args -> Formula a -> Theory a -> Fresh (Tree (Obligation (Theory a)))
obligations args fm thy0 =
  requireAny <$>
    sequence
      [ pack coords <$>
          runPass
            (Induction coords)
            (thy0 { thy_asserts = fm : thy_asserts thy0})
      | coords <- combine [ i | (_,i) <- formulaVars fm `zip` [0..] ]
      ]
  where
  combine xs =
    do i <- [0..indvars args]
       replicateM i xs
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

data Result = Success (Maybe String) | Disproved | Unknown ProcessResult
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
             then Success Nothing
             else Unknown pr
  }

waldmeister :: Prover
waldmeister = Prover
  { prover_cmd = \ filename -> ("waldmeister",filename:["--auto","--output=/dev/stderr","--pcl"])
  , prover_ext = ".w"
  , prover_passes =
      [ TypeSkolemConjecture, Monomorphise False
      , LambdaLift, AxiomatizeLambdas, LetLift
      , SimplifyGently, BoolOpToIf, CommuteMatch, RemoveBuiltinBool
      , SimplifyGently, CollapseEqual, RemoveAliases
      , SimplifyGently, AxiomatizeFuncdefs2, AxiomatizeDatadeclsUEQ
      , SimplifyGently, Monomorphise False
      , SkolemiseConjecture
      ]
  , prover_pretty = Waldmeister.ppTheory . niceRename
  , prover_pipe =
      \ pr@(ProcessResult err out exc) ->
          if "Waldmeister states: Goal proved." `isInfixOf` out
             then Success (Just err)
             else if "Waldmeister states: System completed." `isInfixOf` out
               then Disproved
               else Unknown pr
  }
  where

parsePCL :: String -> IO String
parsePCL s =
  do (exc, out, err) <-
       readProcessWithExitCode
         "proof"
         (words "-nolemmas -nosubst -noplace -nobrackets")
         s

     return (findProof out)
  where
  findProof = unlines . map (reparse . changeTheorem) . drop 2 . dropWhile (/= "Proof:") . lines
  changeTheorem = removeBy . change [("Theorem 1","To show")]

  reparse (' ':xs) = ' ':reparse xs
  reparse [] = []
  reparse xs =
    let (u,v) =  span (/= ' ') xs
    in  beautifyTerm u ++ reparse v

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

newtype Ren = Ren String
  deriving (Eq,Ord,Show)

instance PrettyVar Ren where
  varStr (Ren s) = s

niceRename :: (Ord a,PrettyVar a) => Theory a -> Theory Ren
niceRename thy =
  fmap Ren $
  renameWith (disambig $ suggestWithTypes lcl_rn gbl_rn thy) thy
  where
  lcl_rn (Local x t)
    | is_list t = "xs"
    | otherwise = "x"

  is_list t =
    case fmap varStr t of
      TyCon list _ -> "list" `isInfixOf` map toLower list
      _ -> False

  gbl_rn a (FunctionInfo (PolyType _ [] t))
    | varStr a /= "nil" && is_list t = "as"
    | varStr a /= "nil" && otherwise = "a"
  gbl_rn a _ = varStr a

suggestWithTypes ::
  (Ord a, PrettyVar a) =>
  (Local a -> String) ->
  (a -> GlobalInfo a -> String) ->
  Theory a ->
  (a -> String)
suggestWithTypes lcl_rn gbl_rn thy =
  \ a ->
   case M.lookup a all_locals of
     Just t -> lcl_rn (Local a t)
     Nothing ->
       case lookupGlobal a scp of
         Just gi -> gbl_rn a gi
         Nothing -> varStr a
  where
  all_locals = M.fromList [ (x,t) | Local x t <- universeBi thy ]
  scp        = scope thy

data Term = Node String [Term]
  deriving (Eq,Ord,Show)

toTerm :: Expr String -> Term
toTerm (Lcl (Local x _)) = Node x []
toTerm (Gbl (Global x _ _) :@: xs) = Node x (map toTerm xs)
toTerm (Builtin Equal :@: xs) = Node " = " (map toTerm xs)
toTerm e = error $ "toTerm: " ++ ppRender e

renTerm :: Term -> Term
renTerm (Node s ts) = Node (ren s) (map renTerm ts)
  where
  ren "append" = "++"
  ren "cons"   = ":"
  ren "nil"    = "[]"
  ren s        = s

ppTerm :: Term -> String
ppTerm = go 0 . renTerm
  where
  go _ (Node ":" [t1,Node "[]" []]) = "[" ++ go 0 t1 ++ "]"
  go i (Node s [t1,t2])
    | all op s = par_if (i > 0) (go 1 t1 ++ s ++ go 1 t2)
  go i (Node s []) = s
  go i (Node s as) = par_if (i > 1) (unwords (s:map (go 2) as))

  par_if True  s = "(" ++ s ++ ")"
  par_if False s = s

op x | x `elem` (" :~!@$%^&*_-+=<>.?/" :: String) = True
     | otherwise = False

beautifyTerm :: String -> String
beautifyTerm s = maybe s ppTerm (readTerm s)

readTerm :: String -> Maybe Term
readTerm s =
  case span isAlphaNum s of
    (h,"") -> Just (Node h [])
    (h,t)  -> fmap (Node h) (mapM readTerm =<< matching t)

matching :: String -> Maybe [String]
matching ('(':xs) = go 0 xs
  where
  go i ('(':xs)    = add '(' (go (i+1) xs)
  go 0 (',':xs)    = fmap ([]:) (go 0 xs)
  go 0 (')':xs)    = if null xs then Just [] else Nothing
  go i (')':xs)    = add ')' (go (i-1) xs)
  go i (x:xs)      = add x (go i xs)
  go _ []          = Just []

  add :: Char -> Maybe [String] -> Maybe [String]
  add x (Just [])       = Just [[x]]
  add x (Just (xs:xss)) = Just ((x:xs):xss)
  add _ Nothing         = Nothing

matching s        = Nothing

