{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy

import qualified Cardano.LTL.Lang.Formula.Parser    as Parser
import           Cardano.LTL.Lang.Formula.Yaml
import           Prelude                            hiding (read)

import           Cardano.LTL.Lang.Formula.Parser    (Context (..))
import qualified Cardano.LTL.Lang.Formula.Prec      as Prec
import           Cardano.LTL.Pretty                 (prettyFormula)
import           Cardano.Trace.Feed                 (Filename,
                                                     TemporalEvent (..),
                                                     TemporalEventDurationMicrosec,
                                                     read, readS)
import           Cardano.Trace.Ingest
import           Control.Concurrent                 (threadDelay)
import           Control.Concurrent.Async           (async, cancel,
                                                     forConcurrently_,
                                                     withAsync)
import           Control.Concurrent.MVar
import           Control.Monad                      (when)
import           Data.Aeson
import           Data.Aeson.Encode.Pretty
import           Data.Aeson.Key                     (toText)
import qualified Data.Aeson.KeyMap                  as KeyMap
import           Data.Foldable                      (for_)
import           Data.IORef                         (IORef, newIORef, readIORef)
import           Data.List                          (find)
import qualified Data.Map                           as Map
import           Data.Map.Strict                    (Map)
import           Data.Maybe                         (isJust, mapMaybe)
import qualified Data.Set                           as Set
import           Data.Text                          (Text, intercalate, unpack)
import qualified Data.Text                          as Text
import qualified Data.Text.IO                       as Text
import           Data.Text.Lazy                     (toStrict)
import           Data.Text.Lazy.Builder             (toLazyText)
import           GHC.Generics                       (Generic)
import           Options.Applicative                hiding (Success)
import           Streaming
import           System.Exit                        (die)

#define RETENTION_DEFAULT 200

displayMetrics :: Bool
#ifdef METRICS
displayMetrics = True
#else
displayMetrics = False
#endif

newtype TraceProps = TraceProps { slot :: Int } deriving (Show, Eq, Ord, Generic)

instance FromJSON TraceProps

deriving instance Eq TraceMessage

deriving instance Ord TraceMessage

-- | Extract all accessible properties (fields) from the json object, non-recursively.
--   Accessible fields are all fields of one of the following types: number, string.
extractProps :: Object -> Map PropVarIdentifier PropValue
extractProps = Map.delete "kind" . Map.fromList . mapMaybe parse . KeyMap.toList
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
      Just x  -> Map.insert "host" (TextValue x.tmsgHost)       $
                   Map.insert "thread" (TextValue x.tmsgThread) $
                     extractProps x.tmsgData
      Nothing -> error ("Not an event of type " <> unpack c)
  beg (TemporalEvent t _ _) = t

tabulate :: Int -> Text -> Text
tabulate n = Text.unlines . fmap (Text.replicate n " " <>) . Text.lines

green :: Text -> Text
green text = "\x001b[32m" <> text <> "\x001b[0m"

red :: Text -> Text
red text = "\x001b[31m" <> text <> "\x001b[0m"

prettyTraceMessage :: TraceMessage -> Text
prettyTraceMessage TraceMessage{..} =
  toStrict $ toLazyText $ encodePrettyToTextBuilder  $
    Map.insert "at" (TextValue (Text.show tmsgAt))   $
      Map.insert "namespace" (TextValue tmsgNS)      $
        Map.insert "host" (TextValue tmsgHost)       $
          Map.insert "thread" (TextValue tmsgThread) $
            extractProps tmsgData


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

check :: MVar () -> Formula Text -> [TemporalEvent] -> IO ()
check stdoutLock phi events =
  let result = satisfies phi events
      text = prettySatisfactionResult events phi result in
  withMVar stdoutLock (const $ Text.putStrLn text)

checkS' :: MVar () -> Formula Text -> Stream (Of TemporalEvent) IO () -> IO ()
checkS' stdoutLock phi events = do
  let initial = SatisfyMetrics 0 phi 0
  metrics <- newIORef initial
  withAsync (when displayMetrics $ runDisplay initial metrics) $ \counterDisplayThread -> do
    (consumed, r) <- satisfiesS phi events metrics
    let result = prettySatisfactionResult consumed phi r
    withMVar stdoutLock $ const $ Text.putStrLn result
    cancel counterDisplayThread
  where
    runDisplay :: SatisfyMetrics Text -> IORef (SatisfyMetrics Text) -> IO ()
    runDisplay prev counter = do
      next <- readIORef counter
      withMVar stdoutLock $ const $ do
        putStrLn $ "event/s: " <> show (next.eventsConsumed - prev.eventsConsumed)
        putStrLn $ "Catch-up ratio: "
          <> show ((fromIntegral (next.currentTimestamp - prev.currentTimestamp) :: Double) / 1_000_000)
          <> "  // values above 1.0 <=> realtime"
        Text.putStrLn $ "Formula: " <> prettyFormula next.currentFormula Prec.Universe
      threadDelay 1_000_000 -- 1s
      runDisplay next counter

-- TODO: "Restart" the formula once it is ⊥.
checkOnline :: TemporalEventDurationMicrosec -> Word -> FailureMode -> IngestMode -> [Filename] -> [Formula Text] -> IO ()
checkOnline eventDuration retentionMs failureMode ingestMode files phis = do
  ing <- mkIngestor (fromIntegral retentionMs)
  for_ files (ingestFileThreaded ing failureMode ingestMode)
  stdoutLock <- newMVar ()
  forConcurrently_ phis $ \phi -> async $ do
    reader <- mkIngestorReader ing
    checkS' stdoutLock phi (readS reader eventDuration)

checkOffline :: TemporalEventDurationMicrosec -> Filename -> [Formula Text] -> IO ()
checkOffline eventDuration file phis = do
  events <- read file eventDuration
  stdoutLock <- newMVar ()
  forConcurrently_ phis $ \phi -> async $
    check stdoutLock phi events

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

parseRetention :: Parser Word
parseRetention = option auto $
     long "retention"
  <> metavar "INT"
  <> showDefault
  <> value RETENTION_DEFAULT
  <> help "temporal event retention period before it gets consumed"

data CliOptions = CliOptions
  { formulas      :: Filename
  , mode          :: Mode
  , eventDuration :: Word
  , traces        :: [Filename]
  , retention     :: Word}

parseCliOptions :: Parser CliOptions
parseCliOptions = CliOptions <$> parseFormulasFile <*> parseMode <*> parseEventDuration <*> parseTraceFiles <*> parseRetention

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
  ctx <- Map.toList <$> (readPropValues "sample/context.yaml" >>= dieOnYamlException)
  print ctx
  formulas <- readFormulas options.formulas (Context ctx) Parser.text >>= dieOnYamlException
  let formulas' = fmap (interpTimeunit (\u -> unitToMicrosecond u `div` fromIntegral options.eventDuration)) formulas
  case options.mode of
    Offline -> do
      file <- case options.traces of
        [x] -> pure x
        _   -> die "Only exactly one trace file is supported in 'offline' mode"
      checkOffline options.eventDuration file formulas'
    Online -> do
      checkOnline options.eventDuration options.retention RethrowExceptions FromFileStart options.traces formulas'
  where
    dieOnYamlException :: forall a. Either Exception a -> IO a
    dieOnYamlException (Left exc) = die (Text.unpack exc)
    dieOnYamlException (Right ok) = pure ok
