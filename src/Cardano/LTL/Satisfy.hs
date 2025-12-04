{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Satisfy(
    SatisfactionResult(..)
  , satisfies
  ) where

import           Cardano.Data.Strict
import           Cardano.LTL.Lang
import           Cardano.LTL.Pretty
import           Cardano.LTL.Transform

import           Prelude               hiding (lookup)

import           Data.List             hiding (union)
import qualified Data.Map              as Map
import           Data.Set              (Set, toList, union)
import qualified Data.Set              as Set

import           Data.Text             (unpack)
import           Debug.Trace           (trace, traceShow)

-- | The result of checking satisfaction of a formula against a timeline.
-- | If unsatisfied, stores points in the timeline "relevant" to the formula.
data SatisfactionResult m = Satisfied | Unsatisfied [m] deriving (Show, Eq)

-- | Check if the formula is satisfied in the given event timeline.
satisfies :: (Event m a, Eq a, Show a, Show m) => Foldable f => Formula a -> f m -> SatisfactionResult m
satisfies formula xs = toResult $ foldl' (apply (length xs)) (Quadruple 0 [] formula mempty) xs where
  apply :: (Event m a, Eq a, Show a, Show m) => Int -> Quadruple Int [m] (Formula a) (Set PropValue) -> m -> Quadruple Int [m] (Formula a) (Set PropValue)
  apply total (Quadruple n acc formula idxs) m =
    -- let m = trace ("Message: " <> show m0) m0 in
    -- let formula = trace ("Formula: " <> unpack (prettyFormula formula0 Z) <> "\n") formula0 in
    let !(Relevant !r !formula') = step (trace (show n <> " / " <> show total) formula) m in
    -- let formula'' = trace ("Stepped: " <> unpack (prettyFormula formula' Z) <> "\n") formula' in
    -- let formula''' = trace ("Simplified: " <> unpack (prettyFormula (simplify formula'') Z) <> "\n") (simplify formula'') in
    Quadruple (n + 1) (if r then m : acc else acc) (simplify formula') (allProps m `union` idxs)

  toResult :: Show a => Quadruple Int [m] (Formula a) (Set PropValue) -> SatisfactionResult m
  toResult (Quadruple _ acc formula idxs) = if end (toList idxs) (trace (unpack $ prettyFormula formula Z) formula) then Satisfied else Unsatisfied (reverse acc)
