{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE CPP    #-}
{-# LANGUAGE Strict #-}
module Cardano.LTL.Satisfy(
    SatisfactionResult(..)
  , satisfies
  ) where

import           Cardano.Data.Strict
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Pretty
import           Cardano.LTL.Transform

import           Prelude                                      hiding (lookup)

import           Cardano.LTL.Lang.Internal.GuardedFormula     (GuardedFormula,
                                                               forward,
                                                               toFormula)
import           Cardano.LTL.Lang.Internal.HomogeneousFormula (toGuardedFormula)
import           Data.Text                                    (Text, unpack)
import           Debug.Trace                                  (trace, traceShow)


-- | The result of checking satisfaction of a formula against a timeline.
-- | If unsatisfied, stores points in the timeline "relevant" to the formula.
data SatisfactionResult m = Satisfied | Unsatisfied [m] deriving (Show, Eq)

traceFormula :: Show ty => String -> Formula ty -> Formula ty
traceFormula ~str x =
#ifdef TRACE
  trace (str <> " " <> unpack (prettyFormula x Z)) x
#else
  x
#endif

traceGuardedFormula :: Show ty => String -> GuardedFormula ty -> GuardedFormula ty
traceGuardedFormula ~str x =
#ifdef TRACE
  trace (str <> " " <> unpack (prettyFormula (toFormula x) Z)) x
#else
  x
#endif

-- | Check if the formula is satisfied in the given event timeline.
--   The check is conservative (no false positives) but incomplete (false negatives).
satisfies :: (Event m a, Ord a, Show a, Show m) => Foldable f => Formula a -> f m -> SatisfactionResult m
satisfies formula xs = toResult $ foldl' (apply (length xs)) (Triple 0 [] formula) xs where
  apply :: (Event m a, Ord a, Show a, Show m) => Int -> Triple Int [m] (Formula a) -> m -> Triple Int [m] (Formula a)
  apply total (Triple n acc formula0) m =
    let formula1 = traceFormula ("(" <> show (1 + n) <> " / " <> show total <> ")\ninitial:") formula0 in
    let !(Relevant !r !formula2) = traceGuardedFormula "stepped:" <$> step formula1 m in
    let formula3 = traceGuardedFormula "simplified-next:" (simplifyNext formula2) in
    let formula4 = traceGuardedFormula "simplified-frag:" $ simplifyFragment formula3 in
    let formula5 = traceFormula "forwarded:" (forward formula4) in
    let formula6 = traceFormula "simplified:" (simplify formula5) in
    Triple (n + 1) (if r then m : acc else acc) formula6

  toResult :: (Ord a, Show a) => Triple Int [m] (Formula a) -> SatisfactionResult m
  toResult (Triple _ acc formula) =
    if Top == traceFormula "end:" ((simplify . toFormula . simplifyFragment . toGuardedFormula . terminate) formula)
    then Satisfied
    else Unsatisfied (reverse acc)
