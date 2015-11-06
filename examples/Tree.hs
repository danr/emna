module Tree where

import Tip.Prelude
import qualified Prelude

data Tree a = Empty | Node a (Tree a) (Tree a)

flatten :: Tree a -> [a]
flatten Empty        = []
flatten (Node x p q) = flatten p ++ [x] ++ flatten q

swap :: Tree a -> Tree a
swap Empty        = Empty
swap (Node x p q) = Node x (swap q) (swap p)

spine :: [a] -> Tree a
spine []     = Empty
spine (x:xs) = Node x Empty (spine xs)

ex10 p = flatten (swap p) === reverse (flatten p)








-- ex9 p = size p === length (flatten p)

size :: Tree a -> Nat
size Empty        = Z
size (Node _ p q) = S Z + size p + size q
