module Rotate where

import Tip.Prelude
import qualified Prelude

rotate :: Nat -> [a] -> [a]
rotate Z     xs     = xs
rotate (S _) []     = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

rotlen xs = rotate (length xs) xs === xs
