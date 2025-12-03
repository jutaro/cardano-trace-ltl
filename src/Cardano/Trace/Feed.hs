module Cardano.Trace.Feed(Filename, TemporalEvent, temporalEventLengthMicroseconds, read) where

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

temporalEventLengthMicroseconds :: Word64
temporalEventLengthMicroseconds = 100

-- | Event represents multiple trace messages spanning a range of time of length `temporalEventLengthMicroseconds`.
type TemporalEvent = [TraceMessage]

-- | Fill in one temporal event.
--   Returns the event, the starting time boundary of the next temporal event and the rest of the messages.
fill :: [TraceMessage] -> Word64 -> [TraceMessage] -> (TemporalEvent, Word64, [TraceMessage])
fill acc t (x : xs) | utcToMicroseconds (tmsgAt x) <= t + temporalEventLengthMicroseconds = fill (x : acc) t xs
fill acc t rest = (reverse acc, t + temporalEventLengthMicroseconds, rest)

-- | Slice up the trace messages into consequtive temporal events.
slice :: [TraceMessage] -> [TemporalEvent]
slice [] = []
slice msg@(x : _) = go (utcToMicroseconds (tmsgAt x)) msg where
  go :: Word64 -> [TraceMessage] -> [TemporalEvent]
  go t [] = []
  go t msg =
    let !(e, !t', !msg') = fill [] t msg in
    e : go t' msg'

-- | We assume its possible for the trace messages to come out of order. Remedy that here.
sortByTimestamp :: [TraceMessage] -> [TraceMessage]
sortByTimestamp = sortBy (\x y -> tmsgAt x `compare` tmsgAt y)

read :: Filename -> IO [TemporalEvent]
read filename = do
  traces <- B.lines <$> B.readFile filename
  msgs <- sortByTimestamp <$> traverse throwDecode traces
  let events = slice msgs
  pure events
