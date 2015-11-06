module List where

import Tip
import qualified Prelude

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

conj_append xs ys = xs ++ ys === ys ++ xs


