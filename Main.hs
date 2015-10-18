{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
module Main where

import Tip.HaskellFrontend
import Tip.QuickSpec
import Tip.Core hiding (Unknown)
import Tip.Fresh
import Tip.Passes
import Tip.Pretty
import Tip.Scope
import Tip.Pretty.SMT as SMT

import Debug.Trace

import Tip.Utils.Rename

import Data.Generics.Geniplate

import Data.Maybe
import Data.List (sort, sortBy, isInfixOf, nub)
import Data.Ord
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

import qualified System.IO as IO
import System.Console.CmdArgs
import System.Process (readProcessWithExitCode)

import qualified Data.Map as M
import Data.Map (Map)

data Args =
  Args
    { file    :: String
    , explore :: Bool
    , indvars :: Int
    , timeout :: Double
    , filenames :: Bool
    , prover    :: String
    }
  deriving (Show,Data,Typeable)

defArgs :: Args
defArgs =
  Args
    { file    = ""    &= argPos 0 &= typFile
    , explore = False &= name "e" &= help "Explore theory"
    , indvars = 1     &= name "v" &= help "Number of variables to do induction on"
    , timeout = 1     &= name "t" &= help "Timeout in seconds (default 1)"
    , filenames = False           &= help "Print out filenames of theories"
    , prover = "w"                &= help "Prover (waldmeister/z3)"
    }
  &= program "emna" &= summary "simple inductive prover with proof output"

main :: IO ()
main = do
  args@Args{..} <- cmdArgs defArgs
  x <- readHaskellOrTipFile file defaultParams
  case x of
    Left err  -> putStrLn err
    Right thy ->
      do let p = case prover of
                  'w':_ -> waldmeister
                  'z':_ -> z3
         loop args p =<<
           ((if explore then exploreTheory else return)
            (passes (ren thy)) )
  where
  ren = renameWith (\ x -> [ I i (varStr x) | i <- [0..] ])
  passes =
    head . freshPass
      (runPasses
        [ UncurryTheory
        , SimplifyGently
        , RemoveBuiltinBool
        ])

data I = I Int String
  deriving (Eq,Ord,Show)

instance PrettyVar I where
  varStr (I x s) = s

instance Name I where
  fresh             = refresh (I undefined "x")
  refresh (I _ s)   = do u <- fresh; return (I u s)
  freshNamed s      = refresh (I undefined s)
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
         True  -> go True cs q     thy{ thy_asserts =
                                          let lms = thy_asserts thy
                                          in  makeProved (length lms) c:lms }
         False -> go b    cs (c:q) thy

makeProved :: Int -> Formula a -> Formula a
makeProved i (Formula _ _ tvs b) = Formula Assert (Lemma i) tvs b

formulaVars :: Formula a -> [Local a]
formulaVars = fst . forallView . fm_body

tryProve :: Name a => Args -> Prover -> Formula a -> Theory a -> IO Bool
tryProve args prover fm thy =
  do let tree = freshPass (obligations args fm) thy

     ptree :: Tree (Promise [Obligation Result]) <- T.traverse (promise args prover) tree

     let timeout'     = round (timeout args * 1000 * 1000) -- microseconds
         processes    = 2

     workers (Just timeout') processes (interleave ptree)

     let (prenex,term) =
           forallView $ fm_body $ head $ thy_asserts $ fmap (\ (Ren x) -> x)
             $ niceRename thy thy{thy_asserts = [fm], thy_funcs=[]}

     putStrLn "Considering:"
     putStrLn $ "  " ++ (ppTerm (toTerm term))
     IO.hFlush IO.stdout

     (errs,res) <- evalTree (any (not . isSuccess) . map ob_content) ptree

     case res of
       Obligation (ObInduction coords _ n) _:_
         | sort (map (ind_num . ob_info) res) == [0..n-1]
         , all (isSuccess . ob_content) res
           -> do if null coords
                    then putStrLn $ "Proved without using induction"
                    else putStrLn $ "Proved by induction on " ++ unwords (map (lcl_name . (prenex !!)) coords)
                 let steps =
                       [ do pf <- parsePCL ax_list s
                            putStrLn pf
                       | Obligation _ (Success (Just (s,ax_list))) <- res
                       ]
                 unless (null steps) $ do putStrLn "Proof:"
                                          sequence_ steps

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
      [ do body' <- freshen (fm_body fm)
           pack coords <$>
             runPass
               (Induction coords)
               (thy0 { thy_asserts = fm{ fm_body = body' } : thy_asserts thy0})
      | coords <- combine [ i | (_,i) <- formulaVars fm `zip` [0..] ]
      ]
  where
  combine xs =
    do i <- [0] ++ reverse [1..indvars args]
       us <- replicateM i xs
       guard (nub us == us)
       return us
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

data Result = Success (Maybe (String,AxInfo)) | Disproved | Unknown ProcessResult
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
  , prover_pretty :: forall a . Name a => Theory a -> Theory a -> (Doc,AxInfo)
  , prover_pipe   :: AxInfo -> ProcessResult -> Result
  }

promise :: Name a => Args -> Prover -> Obligation (Theory a) -> IO (Promise [Obligation Result])
promise args Prover{..} (Obligation info thy) =
  do u <- newUnique
     let filename = "/tmp/" ++ show (hashUnique u) ++ prover_ext
     when (filenames args) (putStrLn filename)
     let (thy_pretty,axiom_list) = prover_pretty thy (head (freshPass (runPasses prover_passes) thy))
     writeFile filename (show thy_pretty)
     let (prog,args) = prover_cmd filename
     promise <- processPromise prog args ""

     let update :: PromiseResult ProcessResult -> PromiseResult [Obligation Result]
         update Cancelled = Cancelled
         update Unfinished = Unfinished
         update (An pr) = An [Obligation info (prover_pipe axiom_list pr)]

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
      , SimplifyGently, SkolemiseConjecture
      , SimplifyGently, NegateConjecture
      ]
  , prover_pretty = \ _ thy -> (SMT.ppTheory thy,[])
  , prover_pipe =
      \ _ pr@(ProcessResult err out exc) ->
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
      , CollapseEqual, RemoveAliases
      , AxiomatizeFuncdefs2, AxiomatizeDatadeclsUEQ
      , Monomorphise False
      , SkolemiseConjecture
      ]
  , prover_pretty = \ orig -> Waldmeister.ppTheory . niceRename orig
  , prover_pipe =
      \ ax_list pr@(ProcessResult err out exc) ->
          if "Waldmeister states: Goal proved." `isInfixOf` out
             then Success (Just (err,ax_list))
             else if "Waldmeister states: System completed." `isInfixOf` out
               then Disproved
               else Unknown pr
  }
  where

parsePCL :: AxInfo -> String -> IO String
parsePCL axiom_list s =
  do (exc, out, err) <-
       readProcessWithExitCode
         "proof"
         (words "-nolemmas -nosubst -noplace -nobrackets")
         s

     let axs = mapMaybe unaxiom . lines $ out

     let matches =
           [ (n,i)
           | (n,uv) <- axs
           , (i,st) <- axiom_list
           , matchEq uv st
           ]

     return (findProof matches out
             {-
             ++ "\n" ++ out
             ++ "\n" ++ unlines [ ppTerm e1 ++ " = " ++ ppTerm e2 ++ " " ++ show n | (n,(e1,e2)) <- axs ]
             ++ "\n" ++ unlines [ ppTerm e1 ++ " = " ++ ppTerm e2 ++ " " ++ prettyInfo ax  | (ax,(e1,e2)) <- axiom_list ]
             ++ "\n" ++ "matches: \n" ++
             unlines [ show n ++ " : " ++ prettyInfo i | (n,i) <- matches ]
             ++ "\n" ++ s
             -}
             )
  where
  findProof ms = unlines . fmt . collect ms . drop 2 . dropWhile (/= "Proof:") . lines

  fmt :: ([String],[String],[String]) -> [String]
  fmt (eqs,reasons,thm:_)
    = ( " To show:" ++ reparse (drop (length "  Theorem 1:") thm))
    : [ "     " ++ prettyInfo i ++ ": " ++ ppTerm u ++ " = " ++ ppTerm v
      | (i@(IH _),(u,v)) <- axiom_list
      ] ++
      ""
    : [ h ++ " " ++ u ++ replicate (2 + l - length u) ' ' ++ r
      | (h,(u,r)) <-
          ("  ":repeat " =") `zip`
          (eqs `zip` ("":[ "[" ++ r ++ "]" | r <- reasons ]))
      ]
    where
    l = maximum (0:map length eqs)

  collect :: [(Int,Info String)] -> [String] -> ([String],[String],[String])
  collect ms ((' ':' ':' ':' ':t):ts)
    | Just u <- readTerm t
    , (a,b,c) <- collect ms ts
    = (ppTerm u:a,b,c)
  collect ms ((' ':'=':' ':' ':' ':' ':s):ts)
    | (byax',rest) <- splitAt (length byax) s
    , byax == byax'
    , [(num,blabla)] <- reads rest
    , Just i <- lookup num ms
    , (a,b,c) <- collect ms ts
    = (a,prettyInfo i:b,c)
  collect ms (what:ts)
    | (a,b,c) <- collect ms ts
    = (a,b,what:c)
  collect _ [] = ([],[],[])

  ax = "  Axiom "

  unaxiom s
    | (ax',rest) <- splitAt (length ax) s
    , ax == ax'
    , [(num,':':' ':terms)] <- reads rest
    , (s1,' ':'=':' ':s2) <- break (== ' ') terms
    , Just t1 <- readTerm s1
    , Just t2 <- readTerm s2
    = Just (num :: Int,(t1,t2))
  unaxiom _ = Nothing

  reparse (' ':xs) = ' ':reparse xs
  reparse [] = []
  reparse xs =
    let (u,v) =  span (/= ' ') xs
    in  beautifyTerm u ++ reparse v

  byax = "by Axiom "

prettyInfo :: Info String -> String
prettyInfo i =
  case i of
    Definition f      -> ren f ++ " def"
    IH i              -> "IH" ++ show (i+1)
    Lemma i           -> "lemma " ++ show i
    DataDomain d      -> ""
    DataProjection d  -> d ++ " projection"
    DataDistinct d    -> ""
    Defunction f      -> "by defunctionalisation of " ++ f
    UserAsserted      -> ""
    _                 -> ""

newtype Ren = Ren String
  deriving (Eq,Ord,Show)

instance PrettyVar Ren where
  varStr (Ren s) = case s of
                     "x" -> "v"
                     _   -> s

data Prod f g a = [a] :*: g a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

sND (_ :*: b) = b

niceRename :: (Ord a,PrettyVar a) => Theory a -> Theory a -> Theory Ren
niceRename thy_orig thy =
  sND $
  fmap Ren $
  renameWith (disambig $ suggestWithTypes lcl_rn gbl_rn thy_orig thy)
             (concat interesting :*: thy)
  where
  interesting =
    sortBy (flip $ comparing length)
      [ [ k2 `asTypeOf` k
        | Gbl (Global k2 (PolyType _ [] _) _) :@: _ <- as
        , varStr k2 `notElem` constructors
        ]
      | Formula Prove _ _ fm <- thy_asserts thy
      , Gbl (Global k _ _) :@: as <- universeBi fm
      , varStr k `elem` constructors
      ]

  lcl_rn (Local x t)
    | is "tree" t = "p"
    | is "list" t = "xs"
    | is "nat" t  = "n"
    | is "bool" t = "p"
    | otherwise   = "x"

  is s t =
    case fmap varStr t of
      TyCon list _ -> s `isInfixOf` map toLower list
      _ -> False

  constructors =
    [ varStr k
    | (k,ConstructorInfo{}) <- M.toList (Tip.Scope.globals (scope thy_orig))
    ]

  gbl_rn a _ | varStr a `elem` constructors = varStr a
  gbl_rn a (FunctionInfo (PolyType _ [] t))
    | not (any ((>= 2) . length) interesting)
      || or [ a `elem` xs | xs <- interesting, length xs >= 2 ]
       = case () of
           () | is "list" t -> "as" -- check that a is element in a list with >=2 elements
              | otherwise   -> "a"  -- in the interesting list
    | otherwise = lcl_rn (Local a t)
  gbl_rn a _ = varStr a

suggestWithTypes ::
  (Ord a, PrettyVar a) =>
  (Local a -> String) ->
  (a -> GlobalInfo a -> String) ->
  Theory a ->
  Theory a ->
  (a -> String)
suggestWithTypes lcl_rn gbl_rn thy_orig thy =
  \ a ->
   case M.lookup a all_locals_orig of
     Just t -> lcl_rn (Local a t)
     Nothing ->
       case lookupGlobal a scp_orig of
         Just gi -> gbl_rn a gi
         Nothing ->
           case M.lookup a all_locals of
             Just t -> lcl_rn (Local a t)
             Nothing ->
               case lookupGlobal a scp of
                 Just gi -> gbl_rn a gi
                 Nothing -> varStr a
  where
  all_locals_orig = M.fromList [ (x,t) | Local x t <- universeBi thy_orig ]
  scp_orig        = scope thy_orig
  all_locals      = M.fromList [ (x,t) | Local x t <- universeBi thy ]
  scp             = scope thy

