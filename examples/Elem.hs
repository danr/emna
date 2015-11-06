module Elem where

import Tip
import Tip.Prelude (Nat,(==),Bool(..))
import qualified Prelude

infix 4 ||

(||) :: Bool -> Bool -> Bool
False || b = b
True  || b = True

elem :: Nat -> [Nat] -> Bool
x `elem` []     = False
x `elem` (y:ys) = (x==y) || (x `elem` ys)

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

lemma_or1 x y z = x || (y || z) === (x || y) || z

lemma_assoc xs ys zs = xs ++ (ys ++ zs) === (xs ++ ys) ++ zs

lemma_rid xs = xs ++ [] === xs

conj x xs ys = x `elem` (xs ++ ys) === (x `elem` xs) || (x `elem` ys)

