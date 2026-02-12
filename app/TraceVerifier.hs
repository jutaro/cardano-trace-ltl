{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE LambdaCase          #-}

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
import           Data.Aeson.Key                     (toText)
import qualified Data.Aeson.KeyMap                  as KeyMap
import           Data.Foldable                      (for_, traverse_)
import           Data.IORef                         (newIORef)
import           Data.List                          (find)
import qualified Data.Map                           as Map
import           Data.Map.Strict                    (Map)
import           Data.Maybe                         (isJust, mapMaybe)
import qualified Data.Set                           as Set
import           Data.Text                          (Text, intercalate, pack,
                                                     unpack)
import qualified Data.Text                          as Text
import           Data.Traversable                   (for)
import           GHC.Generics                       (Generic)
import           Options.Applicative                hiding (Success)
import           Streaming
import           System.Exit                        (die)
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
    parse _             = Nothing

instance Event TemporalEvent Text where
  ofTy (TemporalEvent _ msgs _) c = isJust $ find (\msg -> msg.tmsgNS == c) msgs
  index (TemporalEvent _ _ idx) = idx
  props (TemporalEvent _ msgs _) c =
    case find (\msg -> msg.tmsgNS == c) msgs of
      Just x  -> extractProps x.tmsgData
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

checkOnline :: TemporalEventDurationMicrosec -> Int -> FailureMode -> IngestMode -> [Filename] -> [Formula Text] -> IO ()
checkOnline eventDuration minRentionMs failureMode ingestMode files phis = do
  ing <- mkIngestor minRentionMs
  for_ files (ingestFileThreaded ing failureMode ingestMode)
  threads <- for phis $ \phi -> async $ do
    reader <- mkIngestorReader ing
    checkS' phi (readS reader eventDuration)
  traverse_ wait threads

checkOffline :: TemporalEventDurationMicrosec -> Filename -> [Formula Text] -> IO ()
checkOffline eventDuration file phis = do
  events <- read file eventDuration
  threads <- for phis $ \phi -> async $
    check phi events
  traverse_ wait threads


data Mode = Online | Offline deriving (Show, Eq)

readMode :: ReadM Mode
readMode = eitherReader $ \case
  "offline" -> Right Offline
  "online"  -> Right Online
  _         -> Left "Expected either of: 'offline' or 'online'"

parseMode :: Parser Mode
parseMode = option readMode (long "mode" <> metavar "<offline|online>" <> help "mode")

parseEventDuration :: Parser Word
parseEventDuration = option auto (long "duration" <> metavar "INT" <> help "temporal event duration")

parseFormulasFile :: Parser Filename
parseFormulasFile = argument str (metavar "FILE")

parseTraceFiles :: Parser [Filename]
parseTraceFiles = some (argument str (metavar "FILES"))

data CliOptions = CliOptions
  { formulas      :: Filename
  , mode          :: Mode
  , eventDuration :: Word
  , traces        :: [Filename]}

parseCliOptions :: Parser CliOptions
parseCliOptions = CliOptions <$> parseFormulasFile <*> parseMode <*> parseEventDuration <*> parseTraceFiles

opts :: ParserInfo CliOptions
opts = info (parseCliOptions <**> helper)
  ( fullDesc
  <> progDesc "Check formula satisfiability against a log of trace messages"
  <> header "hello - a test for optparse-applicative" )


-- | Convert time unit used in the yaml (currently second) input to μs.
unitToMicrosecond :: Word -> Word
unitToMicrosecond = (1_000_000 *)

main :: IO ()
main = do
  options <- execParser opts
  formulas <- readYaml options.formulas Parser.text >>= dieOnYamlException
  let formulas' = fmap (interpTimeunit (\u -> unitToMicrosecond u `div` fromIntegral options.eventDuration)) formulas
  case options.mode of
    Offline -> do
      file <- case options.traces of
        [x] -> pure x
        _   -> die "Only exactly one trace file is supported in 'offline' mode"
      checkOffline options.eventDuration file formulas'
    Online -> do
      checkOnline options.eventDuration 200 RethrowExceptions FromFileStart options.traces formulas'
  where
    dieOnYamlException :: Either Exception [Formula Text] -> IO [Formula Text]
    dieOnYamlException (Left exc) = die (Text.unpack exc)
    dieOnYamlException (Right ok) = pure ok
