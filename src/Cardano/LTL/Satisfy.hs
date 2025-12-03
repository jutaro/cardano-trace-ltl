{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Satisfy(
    SatisfactionResult(..)
  , satisfies
  ) where

import           Cardano.LTL.Lang
import           Cardano.LTL.Pretty
import           Cardano.LTL.Transform

import           Prelude               hiding (lookup)

import           Data.List             hiding (union)
import qualified Data.Map              as Map
import           Data.Set              (Set, toList, union)
import qualified Data.Set              as Set

import           Data.Text             (unpack)
import           Debug.Trace           (trace)

-- | The result of checking satisfaction of a formula against a timeline.
-- | If unsatisfied, stores points in the timeline "relevant" to the formula.
data SatisfactionResult m = Satisfied | Unsatisfied [m] deriving (Show, Eq)

data Triple a b c = Triple a b c

-- | Check if the formula is satisfied in the given event timeline.
satisfies :: (Event m a, Eq a, Show a, Show m) => Foldable f => Formula a -> f m -> SatisfactionResult m
satisfies formula = toResult . foldl' apply (Triple [] formula mempty) where
  apply :: (Event m a, Eq a, Show a, Show m) => Triple [m] (Formula a) (Set PropValue) -> m -> Triple [m] (Formula a) (Set PropValue)
  apply (Triple acc formula idxs) m =
    -- let m = trace ("Message: " <> show m0) m0 in
    -- let formula = trace ("Formula: " <> unpack (prettyFormula formula0 Z) <> "\n") formula0 in
    let !(Relevant !r !formula') = step formula m in
    -- let formula'' = trace ("Stepped: " <> unpack (prettyFormula formula' Z) <> "\n") formula' in
    -- let formula''' = trace ("Simplified: " <> unpack (prettyFormula (simplify formula'') Z) <> "\n") (simplify formula'') in
    Triple (if r then m : acc else acc) (simplify formula') (Set.fromList (Map.elems (props m)) `union` idxs)

  toResult :: Triple [m] (Formula a) (Set PropValue) -> SatisfactionResult m
  toResult (Triple acc formula idxs) = if end (toList idxs) formula then Satisfied else Unsatisfied (reverse acc)
