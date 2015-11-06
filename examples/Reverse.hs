module Reverse where

import Tip
import qualified Prelude

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

-- lemma_assoc xs ys zs = xs ++ (ys ++ zs) === (xs ++ ys) ++ zs
--
-- lemma_rid xs = xs ++ [] === xs
--
-- lemma xs ys = rev xs ++ rev ys === rev (ys ++ xs)

conj xs = rev (rev xs) === xs

