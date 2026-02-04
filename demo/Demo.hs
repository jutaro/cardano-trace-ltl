{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Check                  (checkFormula)
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy

import           Prelude                            hiding (read)
import qualified Prelude

import           Cardano.LTL.Pretty                 (Lvl (Z), prettyFormula,
                                                     prettyPropKeyValueList)
import           Cardano.Trace.Feed                 (Filename, TemporalEvent(..),
                                                     TemporalEventDurationMicrosec,
                                                     read, readS)
import           Control.Monad                      (unless)
import           Data.Aeson
import           Data.Foldable                      (for_)
import           Data.List                          (find)
import           Data.Map                           (singleton)
import qualified Data.Map                           as Map
import           Data.Maybe                         (isJust)
import           Data.Set                           (fromList)
import qualified Data.Set                           as Set
import           Data.Text                          (Text, intercalate, pack,
                                                     unpack)
import           GHC.Generics                       (Generic)
import           System.Environment                 (getArgs)
import           System.Exit                        (die)
import           Text.Read                          (readMaybe)
import Streaming
import Data.IORef (IORef, newIORef, modifyIORef', readIORef)
import Data.Word (Word64)
import Control.Concurrent (threadDelay, forkIO, killThread)
import qualified Data.Text.IO as Text

newtype TraceProps = TraceProps { slot :: Int } deriving (Show, Eq, Ord, Generic)

instance FromJSON TraceProps

deriving instance Eq TraceMessage

deriving instance Ord TraceMessage

instance Event TemporalEvent Text where
  ofTy (TemporalEvent _ msgs _) c = isJust $ find (\msg -> tmsgNS msg == c) msgs
  index (TemporalEvent _ _ idx) = idx
  props (TemporalEvent _ msgs _) c =
    case find (\msg -> tmsgNS msg == c) msgs of
      Just x ->
        case fromJSON (Object (tmsgData x)) of
          Error err                 -> error ("json parsing error " <> err)
          Success (TraceProps slot) -> singleton "slot" (IntValue slot)
      Nothing -> error ("Not an event of type " <> unpack c)
  beg (TemporalEvent beg _ _) = beg

tabulate :: Int -> Text -> Text
tabulate n = intercalate "\n" . fmap (pack . (replicate n ' ' <>)) . lines . unpack

green :: Text -> Text
green text = "\x001b[32m" <> text <> "\x001b[0m"

red :: Text -> Text
red text = "\x001b[31m" <> text <> "\x001b[0m"

prettyTraceMessage :: TraceMessage -> Text
prettyTraceMessage msg = tmsgNS msg <>
    case fromJSON (Object (tmsgData msg)) of
      Error err                 -> ""
      Success (TraceProps slot) -> "(\"slot\" = " <> pack (show slot) <> ")"


prettyTemporalEvent :: TemporalEvent -> Text
prettyTemporalEvent (TemporalEvent _ msgs _) = intercalate "\n" (fmap prettyTraceMessage msgs)

prettySatisfactionResult :: [TemporalEvent] -> Formula Text -> SatisfactionResult Text -> Text
prettySatisfactionResult events initial Satisfied = prettyFormula initial Z <> " " <> green "(✔)"
prettySatisfactionResult events initial (Unsatisfied rel) =
  prettyFormula initial Z <> red " (✗)" <> "\n"
    <> tabulate 2 (intercalate "\n------\n" (go (Set.toList rel))) where
      go :: [EventIndex] -> [Text]
      go []       = []
      go (e : es) = prettyTemporalEvent (events !! fromIntegral e) : go es

check :: Formula Text -> [TemporalEvent] -> IO ()
check phi events =
  putStrLn (unpack $ prettySatisfactionResult events phi (satisfies phi events))

checkS :: Formula Text -> Stream (Of TemporalEvent) IO () -> IO ()
checkS phi events = do
  let initial = SatisfyMetrics 0 phi 0
  metrics <- newIORef initial
  counterDisplayThread <- forkIO (runDisplay initial metrics)
  (consumed, r) <- satisfiesS phi events metrics
  putStrLn (unpack $ prettySatisfactionResult consumed phi r)
  killThread counterDisplayThread
  where
    updateCounter :: forall a. IORef Word64 -> IO a -> IO a
    updateCounter counter act = modifyIORef' counter (+ 1) >> act

    runDisplay :: SatisfyMetrics Text -> IORef (SatisfyMetrics Text) -> IO ()
    runDisplay prev counter = do
      next <- readIORef counter
      putStrLn $ "event/s: " <> show (next.eventsConsumed - prev.eventsConsumed)
      putStrLn $ "Catch-up ratio: "
        <> show ((fromIntegral (next.currentTimestamp - prev.currentTimestamp) :: Double) / 1_000_000)
        <> "  // values above 1.0 <=> realtime"
      Text.putStrLn $ "Formula: " <> prettyFormula next.currentFormula Z
      threadDelay 1_000_000 -- 1s
      runDisplay next counter

-- ☐ ᪲ (∀i. StartLeadershipCheck("slot" = i) ⇒ ♢(1s) (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)))
prop1 :: TemporalEventDurationMicrosec -> Formula Text
prop1 dur = Forall 0 $ PropForall "i" $
  Implies
    (PropAtom "Forge.Loop.StartLeadershipCheck" (fromList [PropConstraint "slot" (Var "i")]))
    (ExistsN False (floor (1000000 / fromIntegral dur))
      (Or
         [
           PropAtom "Forge.Loop.NodeIsLeader" (fromList [PropConstraint "slot" (Var "i")])
         ,
           PropAtom "Forge.Loop.NodeNotLeader" (fromList [PropConstraint "slot" (Var "i")])
         ]
      )
    )

-- ☐(1s) ᪲ (∀i. (¬ (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)) |˜(1s) StartLeadershipCheck("slot" = i)))
prop2 :: TemporalEventDurationMicrosec -> Formula Text
prop2 dur = Forall (floor (10000000 / fromIntegral dur)) $ PropForall "i" $ UntilN
  True
  (floor (10000000 / fromIntegral dur))
  (Not $
    Or
      [
        PropAtom "Forge.Loop.NodeIsLeader" (fromList [PropConstraint "slot" (Var "i")])
      ,
        PropAtom "Forge.Loop.NodeNotLeader" (fromList [PropConstraint "slot" (Var "i")])
      ]
  )
  (PropAtom "Forge.Loop.StartLeadershipCheck" (fromList [PropConstraint "slot" (Var "i")]))

-- ☐ ᪲ (∀i. ForgedBlock("slot" = i) ⇒ ♢(3s) AdoptedBlock("slot" = i))
prop3 :: TemporalEventDurationMicrosec -> Formula Text
prop3 dur = Forall 0 $ PropForall "i" $ Implies
  (PropAtom "Forge.Loop.ForgedBlock" (fromList [PropConstraint "slot" (Var "i")]))
  (ExistsN False (floor (3000000 / fromIntegral dur))
                 (PropAtom "Forge.Loop.AdoptedBlock" (fromList [PropConstraint "slot" (Var "i")]))
  )

data Mode = Online | Offline


readMode :: String -> Maybe Mode
readMode "online" = Just Online
readMode "offline" = Just Offline
readMode _ = Nothing

readArgs :: [String] -> IO (Filename, Mode, TemporalEventDurationMicrosec)
readArgs [x, readMode -> Just mode ,readMaybe -> Just dur]
                                    = pure (x, mode, dur)
readArgs _                          = die "Usage: $ <filename> <duration>"

main :: IO ()
main = do
  (!filename, !mode, !dur) <- getArgs >>= readArgs
  case mode of
    Offline -> do
      events <- read filename dur
      check (prop1 dur) events
      check (prop2 dur) events
      check (prop3 dur) events
    Online -> do
      let eventStream = readS filename dur
      checkS (prop1 dur) eventStream
      -- checkS (prop2 dur) eventStream
      -- checkS (prop3 dur) eventStream
