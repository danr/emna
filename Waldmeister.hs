{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
module Waldmeister where

import Text.PrettyPrint

import qualified Tip.Pretty.SMT as SMT

import Tip.Pretty
import Tip.Types
import Tip.Core
import Tip.Utils.Rename
import Tip.Utils
import Data.Generics.Geniplate
import Data.Maybe
import Data.Char (isAlphaNum,isDigit)
import Data.List (sortBy)
import Data.Ord (comparing)

import Control.Monad.State
import Control.Monad

validChar :: Char -> String
validChar x
  | isAlphaNum x                             = [x]
  | x `elem` ("~!@$%^&*_-+=<>.?/" :: String) = [x]
  | otherwise                                = ""

type AxInfo = [(Info String,(Term,Term))]

ppTheory :: (Ord a,PrettyVar a) => Theory a -> (Doc,AxInfo)
ppTheory
  (renameWithBlocks keywords
    (disambig (concatMap validChar . varStr))
      -> thy@Theory{..}) =
  (vcat
    [ "NAME" <+> "emna"
    , "MODE" <+> "PROOF"
    , "SORTS" $\ vcat (map (ppVar . sort_name) thy_sorts)
    , "SIGNATURE" $\ vcat (map ppSig thy_sigs)
    , "ORDERING" $\
        vcat
          ["LPO",
           hcat (punctuate " >"
                (map (ppVar . sig_name)
                (reverse
                (sortBy (comparing (length . polytype_args . sig_type))
                        thy_sigs))))]
    , "VARIABLES" $\
        vcat [ ppVar x <+> ":" <+> ppType t
             | Local x t :: Local String <- usort (universeBi thy) ]
    , "EQUATIONS" $\ vcat (map ppFormula as)
    , "CONCLUSION" $\ ppFormula g
    ]
  , [ (i,(toTerm (fmap varStr e1),toTerm (fmap varStr e2)))
    | Formula _ i _ (forallView -> (_,Builtin Equal :@: [e1,e2])) <- as
    ]
  )
  where
  ([g],as) = theoryGoals thy

ppType :: (Ord a, PrettyVar a) => Type a -> Doc
ppType (TyCon t []) = ppVar t
ppType t            = error $ "Waldmeister: cannot handle any sophisticated types: " ++ show (SMT.ppType t)

ppSig :: (Ord a,PrettyVar a) => Signature a -> Doc
ppSig (Signature f (PolyType [] arg_types res_type)) =
  hsep $ [ppVar f,":"] ++ map ppType arg_types ++ ["->",ppType res_type]

ppFormula :: (Ord a, PrettyVar a) => Formula a -> Doc
ppFormula = ppExpr . snd . forallView . fm_body

ppExpr :: (Ord a, PrettyVar a) => Expr a -> Doc
ppExpr (Builtin Equal :@: [e1,e2]) = hsep [ppExpr e1,"=",ppExpr e2]
ppExpr (hd :@: [])  = ppHead hd
ppExpr (hd :@: es)  = hcat ([ppHead hd <> "("] ++ punctuate "," (map ppExpr es)) <> ")"
ppExpr (Lcl l)      = ppVar (lcl_name l)
ppExpr Quant{}      = error "Waldmeister: cannot handle nested quantifiers"
ppExpr Lam{}        = error "Waldmeister: defunctionalize"
ppExpr Match{}      = error "Waldmeister: axiomatize funcdecls and lift matches"
ppExpr Let{}        = error "Waldmeister: lift let declarations"

ppHead :: (Ord a, PrettyVar a) => Head a -> Doc
ppHead (Gbl (Global g _ _)) = ppVar g
ppHead (Builtin (Lit (Bool b))) = text (show b)
ppHead (Builtin b)          = error $ "Waldmeister: cannot handle any builtins! Offending builtin:" ++ show b

keywords :: [String]
keywords = words "> -> : NAME MODE SORTS SIGNATURE ORDERING LPO KBO VARIABLES EQUATIONS CONCLUSION PROOF COMPLETION"

-- Simple terms

data Term = Node String [Term]
  deriving (Eq,Ord,Show)

toTerm :: Expr String -> Term
toTerm (Lcl (Local x _)) = Node x []
toTerm (Gbl (Global x _ _) :@: xs) = Node x (map toTerm xs)
toTerm (Builtin Equal :@: xs) = Node " = " (map toTerm xs)
toTerm (Builtin Implies :@: xs) = Node " => " (map toTerm xs)
toTerm (Builtin At :@: xs) = Node "@" (map toTerm xs)
toTerm (Builtin Not :@: xs) = Node "not" (map toTerm xs)
toTerm (Builtin And :@: xs) = Node "&&" (map toTerm xs)
toTerm (Builtin Or :@: xs) = Node "||" (map toTerm xs)
toTerm (Builtin NumAdd :@: xs) = Node "+"   (map toTerm xs)
toTerm (Builtin NumSub :@: xs) = Node "-"   (map toTerm xs)
toTerm (Builtin NumMul :@: xs) = Node "*"   (map toTerm xs)
toTerm (Builtin NumDiv :@: xs) = Node "/"   (map toTerm xs)
toTerm (Builtin IntDiv :@: xs) = Node "div" (map toTerm xs)
toTerm (Builtin IntMod :@: xs) = Node "mod" (map toTerm xs)
toTerm (Builtin NumGt  :@: xs) = Node ">"   (map toTerm xs)
toTerm (Builtin NumGe  :@: xs) = Node ">="  (map toTerm xs)
toTerm (Builtin NumLt  :@: xs) = Node "<"   (map toTerm xs)
toTerm (Builtin NumLe  :@: xs) = Node "<="  (map toTerm xs)
toTerm (Builtin NumWiden :@: xs) = Node "to_real"  (map toTerm xs)
toTerm (Builtin (Lit (Bool True)) :@: []) = Node "true" []
toTerm (Builtin (Lit (Bool False)) :@: []) = Node "false" []
toTerm (Builtin (Lit (Int x)) :@: []) = Node (show x) []
toTerm (Lam ls e) = Node "\\" (map (\ (Local x _) -> Node x []) ls ++ [toTerm e])
toTerm e = error $ "toTerm: " ++ ppRender e

renTerm :: Term -> Term
renTerm (Node s ts) = Node (ren s) (map renTerm ts)
  where

ren :: String -> String
ren "mult"   = "*"
ren "plus"   = "+"
ren "minus"  = "-"
ren "elem"   = "`elem`"
ren "equals" = "=="
ren "and"    = "&&"
ren "or"     = "||"
ren "append" = "++"
ren "cons"   = ":"
ren "nil"    = "[]"
ren "dot"    = " . "
ren ('a':'p':'p':'l':'y':_) = "@"
ren s        = s

ppTerm :: Term -> String
ppTerm = go 0 . renTerm
  where
  go _ (Node ":" [t1,Node "[]" []]) = "[" ++ go 0 t1 ++ "]"
  go i (Node "@" as) = par_if (i > 1) (unwords (map (go 2) as))
  go i (Node s [t1,t2])
    | any op s = par_if (i > 0) (go 1 t1 ++ s ++ go 1 t2)
  go i (Node s (t1:t2:ts))
    | any op s = par_if (i > 0)
                   (par_if True (go 1 t1 ++ s ++ go 1 t2) ++
                      " " ++ unwords (map (go 1) ts))
  go i (Node s []) = s
  go i (Node "\\" as) =
    let (vs,[e]) = splitAt (length as - 1) as
    in  par_if (i > 1) ("\\ " ++ unwords (map (go 0) vs) ++ " -> " ++ go 0 e)
  go i (Node s as) = par_if (i > 1) (unwords (s:map (go 2) as))

  par_if True  s = "(" ++ s ++ ")"
  par_if False s = s :: String

ppEquation :: (Term,Term) -> String
ppEquation (u,v) = ppTerm u ++ " = " ++ ppTerm v

op x | x `elem` (" `:~!@$%^&*_-+=<>.?/|" :: String) = True
     | otherwise = False

beautifyTerm :: String -> String
beautifyTerm s = maybe s ppTerm (readTerm s)

readTerm :: String -> Maybe Term
readTerm s =
  case span isAlphaNum s of
    (h,"") -> Just (Node h [])
    (h,t)  -> fmap (Node h) (mapM readTerm =<< matching t)

readEquation :: String -> Maybe (Term,Term)
readEquation s
  | (s1,' ':'=':' ':s2) <- break (== ' ') s
  , Just t1 <- readTerm s1
  , Just t2 <- readTerm s2
  = Just (t1,t2)
readEquation _ = Nothing

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

matchEq :: (Term,Term) -> (Term,Term) -> Bool
matchEq (u,v) (s,t) =
  or [ match (Node "" uv) (Node "" [s,t])
     | uv <- [[u,v],[v,u]]
     ]

match :: Term -> Term -> Bool
match t1 t2 = evalState (go t1 t2) []
  where
  go :: Term -> Term -> State [(String,Term)] Bool
  go (Node s@('x':r) []) t | all isDigit r =
    do m <- gets (lookup s)
       case m of
         Nothing -> do modify ((s,t):)
                       return True
         Just t' -> do return (t == t')
  go (Node a as) (Node b bs) =
    do let ok1 = a == b
       let ok2 = length as == length bs
       oks <- zipWithM go as bs
       return (and (ok1:ok2:oks))

nodesOf :: Term -> [String]
nodesOf (Node s xs) = s:concatMap nodesOf xs

nodesOfEq :: (Term,Term) -> [String]
nodesOfEq (u,v) = nodesOf u ++ nodesOf v

