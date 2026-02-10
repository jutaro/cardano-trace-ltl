{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy

import qualified Cardano.LTL.Lang.Formula.Parser    as Parser
import           Cardano.LTL.Lang.Formula.Yaml
import           Prelude                            hiding (read)

import qualified Cardano.LTL.Lang.Formula.Prec      as Prec
import           Cardano.LTL.Pretty                 (prettyFormula)
import           Cardano.Trace.Feed                 (Filename,
                                                     TemporalEvent (..),
                                                     TemporalEventDurationMicrosec,
                                                     read, readS)
import           Cardano.Trace.Ingest
import           Control.Concurrent.Async           (async, wait)
import           Data.Aeson
import           Data.Foldable                      (for_, traverse_)
import           Data.IORef                         (newIORef)
import           Data.List                          (find)
import           Data.Map                           (singleton)
import           Data.Maybe                         (isJust, mapMaybe)
import           Data.Set                           (fromList)
import qualified Data.Set                           as Set
import           Data.Text                          (Text, intercalate, pack,
                                                     unpack)
import           Data.Traversable                   (for)
import           GHC.Generics                       (Generic)
import           Streaming
import           System.Environment                 (getArgs)
import           System.Exit                        (die)
import           Text.Read                          (readMaybe)
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import qualified Data.Map as Map
import qualified Data.Aeson.KeyMap as KeyMap
import Debug.Trace (trace)
import Data.Aeson.Key (toText)
#ifdef METRICS
import           Control.Concurrent                 (forkIO, killThread,
                                                     threadDelay)
import           Data.IORef                         (IORef, readIORef)
import qualified Data.Text.IO                       as Text
#endif

newtype TraceProps = TraceProps { slot :: Int } deriving (Show, Eq, Ord, Generic)

instance FromJSON TraceProps

deriving instance Eq TraceMessage

deriving instance Ord TraceMessage

extractProps :: Object -> Map PropVarIdentifier PropValue
extractProps = Map.fromList . mapMaybe parse . KeyMap.toList
  where
    parse :: (Key, Value) -> Maybe (PropVarIdentifier, PropValue)
    parse (k, Number v) = Just (toText k, IntValue (truncate v))
    parse (k, String v) = Just (toText k, TextValue v)
    parse _ = Nothing

instance Event TemporalEvent Text where
  ofTy (TemporalEvent _ msgs _) c = isJust $ find (\msg -> msg.tmsgNS == c) msgs
  index (TemporalEvent _ _ idx) = idx
  props (TemporalEvent _ msgs _) c =
    case find (\msg -> msg.tmsgNS == c) msgs of
      Just x -> extractProps x.tmsgData
      Nothing -> error ("Not an event of type " <> unpack c)
  beg (TemporalEvent t _ _) = t

tabulate :: Int -> Text -> Text
tabulate n = intercalate "\n" . fmap (pack . (replicate n ' ' <>)) . lines . unpack

green :: Text -> Text
green text = "\x001b[32m" <> text <> "\x001b[0m"

red :: Text -> Text
red text = "\x001b[31m" <> text <> "\x001b[0m"

prettyTraceMessage :: TraceMessage -> Text
prettyTraceMessage msg = tmsgNS msg <>
    case fromJSON (Object (tmsgData msg)) of
      Error _                   -> ""
      Success (TraceProps slot) -> "(\"slot\" = " <> pack (show slot) <> ")"


prettyTemporalEvent :: TemporalEvent -> Text -> Text
prettyTemporalEvent (TemporalEvent _ msgs _) ns =
  maybe (intercalate "\n" (fmap prettyTraceMessage msgs) <> "  // " <> ns) prettyTraceMessage (find (\ x -> x.tmsgNS == ns) msgs)

prettySatisfactionResult :: [TemporalEvent] -> Formula Text -> SatisfactionResult Text -> Text
prettySatisfactionResult _ initial Satisfied = prettyFormula initial Prec.Universe <> " " <> green "(✔)"
prettySatisfactionResult events initial (Unsatisfied rel) =
  prettyFormula initial Prec.Universe <> red " (✗)" <> "\n"
    <> tabulate 2 (intercalate "\n------\n" (go (Set.toList rel))) where
      go :: [(EventIndex, Text)] -> [Text]
      go []       = []
      go ((e, ty) : es) = prettyTemporalEvent (events !! fromIntegral e) ty : go es

check :: Formula Text -> [TemporalEvent] -> IO ()
check phi events =
  putStrLn (unpack $ prettySatisfactionResult events phi (satisfies phi events))

checkS' :: Formula Text -> Stream (Of TemporalEvent) IO () -> IO ()
checkS' phi events = do
  let initial = SatisfyMetrics 0 phi 0
  metrics <- newIORef initial
#ifdef METRICS
  counterDisplayThread <- forkIO (runDisplay initial metrics)
#endif
  (consumed, r) <- satisfiesS phi events metrics
  putStrLn (unpack $ prettySatisfactionResult consumed phi r)
#ifdef METRICS
  killThread counterDisplayThread
#endif
#ifdef METRICS
  where
    runDisplay :: SatisfyMetrics Text -> IORef (SatisfyMetrics Text) -> IO ()
    runDisplay prev counter = do
      next <- readIORef counter
      putStrLn $ "event/s: " <> show (next.eventsConsumed - prev.eventsConsumed)
      putStrLn $ "Catch-up ratio: "
        <> show ((fromIntegral (next.currentTimestamp - prev.currentTimestamp) :: Double) / 1_000_000)
        <> "  // values above 1.0 <=> realtime"
      Text.putStrLn $ "Formula: " <> prettyFormula next.currentFormula Prec.Universe
      threadDelay 1_000_000 -- 1s
      runDisplay next counter
#endif

checkRealtime :: TemporalEventDurationMicrosec -> Int -> FailureMode -> IngestMode -> [Filename] -> [Formula Text] -> IO ()
checkRealtime eventDuration minRentionMs failureMode ingestMode files phis = do
  ing <- mkIngestor minRentionMs
  for_ files (ingestFileThreaded ing failureMode ingestMode)
  threads <- for phis $ \phi -> async $ do
    reader <- mkIngestorReader ing
    checkS' phi (readS reader eventDuration)
  traverse_ wait threads


-- ☐ ᪲ (∀i. StartLeadershipCheck("slot" = i) ⇒ ♢(1s) (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)))
prop1 :: TemporalEventDurationMicrosec -> Formula Text
prop1 dur = Forall 0 $ PropForall "i" $
  Implies
    (PropAtom "Forge.Loop.StartLeadershipCheck" (fromList [PropConstraint "slot" (Var "i")]))
    (ExistsN (floor ((1000000 :: Double) / fromIntegral dur)) $
      Or
        (PropAtom "Forge.Loop.NodeIsLeader" (fromList [PropConstraint "slot" (Var "i")]))
        (PropAtom "Forge.Loop.NodeNotLeader" (fromList [PropConstraint "slot" (Var "i")]))

    )

-- ☐ ᪲(1s) (∀i. (¬ (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)) |˜(1s) StartLeadershipCheck("slot" = i)))
prop2 :: TemporalEventDurationMicrosec -> Formula Text
prop2 dur = Forall (floor ((1000000 :: Double) / fromIntegral dur)) $ PropForall "i" $ UntilN
  (floor ((1000000 :: Double) / fromIntegral dur))
  (Not $
    Or
      (PropAtom "Forge.Loop.NodeIsLeader" (fromList [PropConstraint "slot" (Var "i")]))
      (PropAtom "Forge.Loop.NodeNotLeader" (fromList [PropConstraint "slot" (Var "i")]))
  )
  (PropAtom "Forge.Loop.StartLeadershipCheck" (fromList [PropConstraint "slot" (Var "i")]))

-- ☐ ᪲ (∀i. ForgedBlock("slot" = i) ⇒ ♢(3s) AdoptedBlock("slot" = i))
prop3 :: TemporalEventDurationMicrosec -> Formula Text
prop3 dur = Forall 0 $ PropForall "i" $ Implies
  (PropAtom "Forge.Loop.ForgedBlock" (fromList [PropConstraint "slot" (Var "i")]))
  (ExistsN (floor ((3000000 :: Double) / fromIntegral dur))
           (PropAtom "Forge.Loop.AdoptedBlock" (fromList [PropConstraint "slot" (Var "i")]))
  )

data Mode = Online | Offline


readMode :: String -> Maybe Mode
readMode "online"  = Just Online
readMode "offline" = Just Offline
readMode _         = Nothing

readArgs :: [String] -> IO (Filename, Mode, TemporalEventDurationMicrosec, [Filename])
readArgs (phis : (readMode -> Just mode) : (readMaybe -> Just dur) : "--" : traces)
                                    = pure (phis, mode, dur, traces)
readArgs _                          = die "Usage: $ <filename> <offline|online> <duration> -- [<filename>]"

main :: IO ()
main = do
  (!formulasFile, !mode, !dur, !traces) <- getArgs >>= readArgs
  case mode of
    Offline -> do
      let [file] = traces
      events <- read file dur
      check (prop1 dur) events
      check (prop2 dur) events
      check (prop3 dur) events
    Online -> do
      formulas <- readYaml formulasFile Parser.text >>= dieOnYamlException
      let formulas' = fmap (interpTimeunit (\sec -> sec * 1_000_000 `div` fromIntegral dur)) formulas
      for_ formulas' print
      checkRealtime dur 200 RethrowExceptions FromFileStart traces formulas'
  where
    dieOnYamlException :: Either Exception [Formula Text] -> IO [Formula Text]
    dieOnYamlException (Left exc) = die (Text.unpack exc)
    dieOnYamlException (Right ok) = pure ok
