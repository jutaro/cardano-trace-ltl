{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Satisfy(
    SatisfactionResult(..)
  , satisfies
  ) where

import           Cardano.LTL.Lang
import           Cardano.LTL.Transform
import           Data.List             hiding (union)
import qualified Data.Map              as Map
import           Data.Set              (Set, toList, union)
import qualified Data.Set              as Set
import           Prelude               hiding (lookup)

-- | The result of checking satisfaction of a formula against a timeline.
-- | If unsatisfied, stores points in the timeline "relevant" to the formula.
data SatisfactionResult m = Satisfied | Unsatisfied [m] deriving (Show, Eq)

-- | Check if the formula is satisfied in the given event timeline.
satisfies :: (Event m a, Eq a, Show a, Show m) => Foldable f => Formula a -> f m -> SatisfactionResult m
satisfies formula = toResult . foldl' apply ([], formula, mempty) where
  apply :: (Event m a, Eq a, Show a, Show m) => ([m], Formula a, Set PropValue) -> m -> ([m], Formula a, Set PropValue)
  apply (acc, formula, idxs) m =
    let !(Relevant !r !formula') = step formula m in
    (if r then m : acc else acc, {-trace (pretty formula' Z <> "\n") -} formula', Set.fromList (Map.elems (props m)) `union` idxs)

  toResult :: ([m], Formula a, Set PropValue) -> SatisfactionResult m
  toResult (acc, formula, idxs) = if end (toList idxs) formula then Satisfied else Unsatisfied (reverse acc)
