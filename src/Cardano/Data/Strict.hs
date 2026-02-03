module Cardano.Data.Strict(Pair(..), Triple(..), Quadruple(..), Quintuple(..), SnocList(..), (<>>)) where

data Pair a b = Pair a b deriving (Show, Eq, Ord)

data Triple a b c = Triple a b c deriving (Show, Eq, Ord)

data Quadruple a b c d = Quadruple a b c d deriving (Show, Eq, Ord)

data Quintuple a b c d e = Quintuple a b c d e deriving (Show, Eq, Ord)

data SnocList a = Lin | SnocList a :< a

infix 5 <>>
(<>>) :: SnocList a -> [a] -> [a]
Lin <>> ys = ys
xs :< x <>> ys = xs <>> (x : ys)
