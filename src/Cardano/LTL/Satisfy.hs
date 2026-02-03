{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE Strict              #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
module Cardano.LTL.Satisfy(
    SatisfactionResult(..)
  , satisfies
  , satisfiesS
  , SatisfyMetrics(..)
  ) where

import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Transform

import           Prelude                                      hiding (lookup)

import           Cardano.LTL.Lang.Internal.GuardedFormula     (GuardedFormula,
                                                               forward)
import           Cardano.LTL.Lang.Internal.HomogeneousFormula (interp)
import           Data.IORef                                   (IORef,
                                                               modifyIORef')
import           Data.Set                                     (Set)
import           Data.Word                                    (Word64)
import           Streaming
#ifdef TRACE
import           Cardano.LTL.Lang.Internal.GuardedFormula     (toFormula)
import qualified Cardano.LTL.Prec                             as Prec
import           Cardano.LTL.Pretty                           (prettyFormula)
import qualified Data.Text                                    as Text
import           Debug.Trace                                  (trace)
#endif



-- | The result of checking satisfaction of a formula against a timeline.
-- | If unsatisfied, stores points in the timeline "relevant" to the formula.
data SatisfactionResult ty = Satisfied | Unsatisfied (Set EventIndex) deriving (Show, Eq)

traceFormula :: Show ty => String -> Formula ty -> Formula ty
traceFormula ~str x =
#ifdef TRACE
  trace (str <> " " <> Text.unpack (prettyFormula x Prec.Universe)) x
#else
  x
#endif

traceGuardedFormula :: Show ty => String -> GuardedFormula ty -> GuardedFormula ty
traceGuardedFormula ~str x =
#ifdef TRACE
  trace (str <> " " <> Text.unpack (prettyFormula (toFormula x) Prec.Universe)) x
#else
  x
#endif

handleNext :: (Event event ty, Eq ty, Show ty) => (Int, Formula ty) -> event -> Either (SatisfactionResult ty) (Int, Formula ty)
handleNext (!n, !formula0) m =
  let formula1 = traceFormula ("(" <> show (1 + n) <> ")\ninitial:") formula0 in
  let formula2 = traceGuardedFormula "stepped:" $ step formula1 m in
  let formula3 = traceGuardedFormula "simplified-next:" (simplifyNext formula2) in
  let formula30 = traceGuardedFormula "simplified-homogeneous:" (simplifyHomogeneous formula3) in
  let formula4 = traceGuardedFormula "simplified-frag:" $ simplifyFragment formula30 in
  let formula5 = traceFormula "forwarded:" (forward formula4) in
  let formula6 = traceFormula "simplified:" (simplify formula5) in
  case formula6 of
    Top     -> Left Satisfied
    Bottom  -> Left (Unsatisfied (relevant formula0))
    formula -> Right (n + 1, formula6)

handleEnd :: (Eq ty, Show ty) => (Int, Formula ty) -> SatisfactionResult ty
handleEnd (!n, !formula) =
    if (interp . terminate) formula
    then Satisfied
    else Unsatisfied (relevant formula)

merge :: Either a a -> a
merge = either id id

-- | Check if the formula is satisfied in the given event timeline.
satisfies :: (Event event ty, Ord ty, Show ty) => Foldable f => Formula ty -> f event -> SatisfactionResult ty
satisfies formula xs = merge $ handleEnd <$> foldl' (\acc e -> acc >>= flip handleNext e) (Right (0, formula)) xs


data SatisfyMetrics ty = SatisfyMetrics {
  eventsConsumed   :: Word64,
  currentFormula   :: Formula ty,
  -- | μs
  currentTimestamp :: Word64
}

-- | Given a formula and a stream of events, forms a `Monad` computation that returns a `SatisfactionResult` once
--    the formula is equivalent to ⊤ or ⊥. This may happen either once the stream terminates or if
--    the formula is falsified early by some prefix of the stream.
satisfiesS :: (Event event ty, Ord ty, Show ty)
           => Formula ty
           -> Stream (Of event) IO ()
           -> IORef (SatisfyMetrics ty)
           -> IO ([event], SatisfactionResult ty)
satisfiesS formula input metrics = run $ mapped (pure. pure . runIdentity) $ unfold (go metrics) (0, formula, [], input) where
  go :: (Ord ty, Event event ty, Show ty)
     => IORef (SatisfyMetrics ty)
     -> (Int, Formula ty, [event], Stream (Of event) IO ())
     -> IO (Either ([event], SatisfactionResult ty) (Identity (Int, Formula ty, [event], Stream (Of event) IO ())))
  go metrics (!n, !formula, !consumed, !input) = inspect input >>= \case
    Left () -> pure $ Left
      (consumed, handleEnd (n, formula))
    Right (event :> more) -> do
      let consumed' = event : consumed
      modifyIORef' metrics (\x -> SatisfyMetrics (1 + x.eventsConsumed) formula (beg event))
      pure $
        bimap (consumed',)
            (\(!n', !formula') -> Identity (n', formula', consumed', more))
            (handleNext (n, formula) event)
