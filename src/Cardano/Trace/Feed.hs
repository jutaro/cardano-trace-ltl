{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedRecordDot   #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE MultiWayIf #-}

module Cardano.Trace.Feed(Filename, TemporalEvent(..), TemporalEventDurationMicrosec, read, readS, verify) where

import           Cardano.Logging.Types.TraceMessage
import qualified Data.ByteString.Lazy.Char8         as BL

import           Prelude                            hiding (read)

import           Cardano.Data.Strict                (SnocList (..), (<>>))
import           Data.Aeson                         (parseJSON,
                                                     throwDecodeStrict, encode)
import           Data.Aeson.Decoding                (throwDecode)
import qualified Data.ByteString.Char8              as BChar8
import           Data.List                          (sortBy)
import           Data.Maybe                         (isNothing)
import           Data.Time.Clock                    (UTCTime)
import           Data.Time.Clock.POSIX              (utcTimeToPOSIXSeconds)
import           Data.Word                          (Word64)
import           GHC.IO.Handle                      (Handle, hIsEOF)
import           GHC.IO.IOMode                      (IOMode (WriteMode))
import           Streaming
import           Streaming.Prelude                  (yield)
import           System.Exit                        (die)
import           System.IO                          (FilePath,
                                                     IOMode (ReadMode),
                                                     openFile)

-- TODO: Stream

type Filename = String

utcToMicroseconds :: UTCTime -> Word64
utcToMicroseconds utcTime = round $ utcTimeToPOSIXSeconds utcTime * 1000000

-- | Temporal event represents multiple trace messages spanning some duration of time together with an index of the event.
data TemporalEvent = TemporalEvent {
  -- | Microseconds since epoch when the event begins.
  beg :: Word64,
  messages :: [TraceMessage],
  idx :: Int
}

-- | For performance considerations we group trace messages within the specified duration in one `TemporalEvent`.
type TemporalEventDurationMicrosec = Word64

-- | Fill in one temporal event.
--   Returns the event, the starting time boundary of the next temporal event and the rest of the messages.
fill :: Int -> TemporalEventDurationMicrosec -> [TraceMessage] -> Word64 -> [TraceMessage] -> (TemporalEvent, Word64, [TraceMessage], Int)
fill idx duration acc t (x : xs) | utcToMicroseconds x.tmsgAt  <= t + duration = fill idx duration (x : acc) t xs
fill idx duration acc t rest = (TemporalEvent t (reverse acc) idx, t + duration, rest, idx + 1)

-- | Slice up the trace messages into consequtive temporal events.
slice :: TemporalEventDurationMicrosec -> [TraceMessage] -> [TemporalEvent]
slice duration [] = []
slice duration msg@(x : _) = go 0 (utcToMicroseconds (tmsgAt x)) msg where
  go :: Int -> Word64 -> [TraceMessage] -> [TemporalEvent]
  go idx t [] = []
  go idx t msg =
    let (e, !t', !msg', !idx') = fill idx duration [] t msg in
    e : go idx' t' msg'

-- | We assume its possible for the trace messages to come out of order. Remedy that here.
sortByTimestamp :: [TraceMessage] -> [TraceMessage]
sortByTimestamp = sortBy (\x y -> tmsgAt x `compare` tmsgAt y)

-- | Read a text file where every line is a json object representation of a `TraceMessage`.
--   Trace messages lying within the specified `TemporalEventDurationMicrosec` are grouped in `TemporalEvent`.
--   The trace messages are sorted by timestamp before any action.
read :: Filename -> TemporalEventDurationMicrosec -> IO [TemporalEvent]
read filename duration = do
  traces <- BChar8.lines <$> BChar8.readFile filename
  msgs <- {- sortByTimestamp <$> -} traverse throwDecodeStrict traces
  let events = slice duration msgs
  pure events

readLine :: Handle -> IO (Maybe TraceMessage)
readLine handle = hIsEOF handle >>= \case
  True -> pure Nothing
  False -> do
    line <- BChar8.hGetLine handle
    throwDecodeStrict line

writeLine :: Handle -> TraceMessage -> IO ()
writeLine handle msg = BChar8.hPutStrLn handle (BChar8.toStrict $ encode msg)

data TemporalEventBuilderSt = TemporalEventBuilderSt {
  -- | A message read from the file that hasn't been distributed yet (if any).
  nextBuffered :: !(Maybe TraceMessage),
  -- | Next issued temporal event ordinal.
  nextIdx      :: !Int,
  -- | The timestamp of the beginning of the next issued temporal event.
  nextBeg      :: !Word64,
  -- | The accumulation of trace messages to be issued in the next issued temporal event.
  nextMsgs     :: !(SnocList TraceMessage),
  -- | Whether the file of trace messages has ended.
  nextTerminal :: !Bool
}

verify :: Filename -> Filename -> IO ()
verify input output = do
  inputH <- openFile input ReadMode
  outputH <- openFile output WriteMode
  readLine inputH >>= \case
    Nothing -> pure ()
    Just msg -> do
      writeLine outputH msg
      go inputH outputH 2 msg.tmsgAt

  where
    go inputH outputH lineNum prev = do
      readLine inputH >>= \case
        Nothing -> pure ()
        Just msg ->
          if utcToMicroseconds prev <= utcToMicroseconds msg.tmsgAt
          then do
            writeLine outputH msg
            go inputH outputH (lineNum + 1) msg.tmsgAt
          else prompt
           where
            prompt = do
              BChar8.putStrLn (BChar8.toStrict $ encode msg)
              putStrLn $ "  @ line " <> show lineNum <> ", remove (y/n)?"
              line <- getLine
              if
                | line == "" || line == "y" ->
                  go inputH outputH (lineNum + 1) prev
                | line == "n" -> do
                  writeLine outputH msg
                  go inputH outputH (lineNum + 1) msg.tmsgAt
                | otherwise -> prompt




-- TODO: Support multiple files. The input shall be sorted and buffered for a configurable
-- period of time. Once the time elapses, the input shall be sorted.
-- This is a prevention measure for the trace messages appearing out of order sometime.
readS :: Filename -> TemporalEventDurationMicrosec -> Stream (Of TemporalEvent) IO ()
readS filename duration = do
  handle <- lift $ openFile filename ReadMode
  lift (readLine handle) >>= \case
    Nothing -> pure ()
    Just firstMsg -> do
      unfold (go handle) $
       TemporalEventBuilderSt
         { nextBuffered = Just firstMsg
         , nextIdx = 0
         , nextBeg = utcToMicroseconds firstMsg.tmsgAt
         , nextMsgs = Lin
         , nextTerminal = False
         }
  where
    go :: Handle
      -> TemporalEventBuilderSt
      -> IO (Either () (Of TemporalEvent TemporalEventBuilderSt))
    go handle TemporalEventBuilderSt{nextTerminal = True, ..} = pure (Left ())
    go handle TemporalEventBuilderSt{nextBuffered = Nothing, ..} = readLine handle >>= \case
      Nothing -> pure $ Right $
        TemporalEvent nextBeg (nextMsgs <>> []) nextIdx
          :>
        TemporalEventBuilderSt Nothing (nextIdx + 1) nextBeg Lin True
      Just msg ->
        go handle (TemporalEventBuilderSt (Just msg) nextIdx nextBeg nextMsgs False)
    go handle TemporalEventBuilderSt{nextBuffered = Just msg, ..} | utcToMicroseconds msg.tmsgAt <= nextBeg + duration =
        go handle (TemporalEventBuilderSt Nothing nextIdx nextBeg (nextMsgs :< msg) False)
    go handle TemporalEventBuilderSt{nextBuffered = Just msg, ..} = pure $ Right $
      TemporalEvent nextBeg (nextMsgs <>> []) nextIdx
        :>
      TemporalEventBuilderSt (Just msg) (nextIdx + 1) (nextBeg + duration) Lin False
