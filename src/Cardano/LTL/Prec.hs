module Cardano.LTL.Prec where

data Prec = Universe | Implies | Or | And | Prefix | Eq | Atom deriving (Show, Eq, Ord)
