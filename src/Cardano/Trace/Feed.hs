module Cardano.Trace.Feed(Filename, TemporalEvent, TemporalEventDurationMicrosec, read) where

import           Cardano.Logging.Types.TraceMessage

import           Prelude                            hiding (read)

import           Codec.Serialise
import           Data.Aeson                         (parseJSON)
import           Data.Aeson.Decoding                (throwDecode)
import           Data.ByteString.Lazy               (ByteString)
import qualified Data.ByteString.Lazy.Char8         as B
import           Data.List                          (sortBy)
import           Data.Time.Clock                    (UTCTime)
import           Data.Time.Clock.POSIX              (utcTimeToPOSIXSeconds)
import           Data.Word                          (Word64)
import           System.IO                          (FilePath)

-- TODO: Stream

type Filename = String

utcToMicroseconds :: UTCTime -> Word64
utcToMicroseconds utcTime = round $ utcTimeToPOSIXSeconds utcTime * 1000000

-- | Temporal event represents multiple trace messages spanning some duration of time together with an index of the event.
type TemporalEvent = ([TraceMessage], Int)

-- | For performance considerations we group trace messages within the specified duration in one `TemporalEvent`.
type TemporalEventDurationMicrosec = Word64

-- | Fill in one temporal event.
--   Returns the event, the starting time boundary of the next temporal event and the rest of the messages.
fill :: Int -> TemporalEventDurationMicrosec -> [TraceMessage] -> Word64 -> [TraceMessage] -> (TemporalEvent, Word64, [TraceMessage], Int)
fill idx duration acc t (x : xs) | utcToMicroseconds (tmsgAt x) <= t + duration = fill idx duration (x : acc) t xs
fill idx duration acc t rest = ((reverse acc, idx), t + duration, rest, idx + 1)

-- | Slice up the trace messages into consequtive temporal events.
slice :: TemporalEventDurationMicrosec -> [TraceMessage] -> [TemporalEvent]
slice duration [] = []
slice duration msg@(x : _) = go 0 (utcToMicroseconds (tmsgAt x)) msg where
  go :: Int -> Word64 -> [TraceMessage] -> [TemporalEvent]
  go idx t [] = []
  go idx t msg =
    let !(e, !t', !msg', !idx') = fill idx duration [] t msg in
    e : go idx' t' msg'

-- | We assume its possible for the trace messages to come out of order. Remedy that here.
sortByTimestamp :: [TraceMessage] -> [TraceMessage]
sortByTimestamp = sortBy (\x y -> tmsgAt x `compare` tmsgAt y)

-- | Read a text file where every line is a json object representation of a `TraceMessage`.
--   Trace messages lying within the specified `TemporalEventDurationMicrosec` are grouped in on `TemporalEvent`.
--   The trace messages are sorted by timestamp before any action.
read :: Filename -> TemporalEventDurationMicrosec -> IO [TemporalEvent]
read filename duration = do
  traces <- B.lines <$> B.readFile filename
  msgs <- sortByTimestamp <$> traverse throwDecode traces
  let events = slice duration msgs
  pure events
