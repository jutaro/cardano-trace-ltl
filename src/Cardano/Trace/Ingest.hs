{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Cardano.Trace.Ingest
       ( Ingestor
       , mkIngestor
       , readLineIngestor
       , ingestFileThreaded
       ) where

import Control.Concurrent
import Control.Concurrent.STM.TQueue
import Control.Concurrent.STM.TVar
import Control.Exception
import Control.Monad (forever, forM_, void, when)
import Control.Monad.STM (atomically)
import Data.Aeson (FromJSON(..), decodeStrict', withObject, (.:))
import Data.ByteString.Char8 as ByteString (ByteString, hGetLine)
import qualified Data.Map.Strict as Map
import Data.Time.Clock (NominalDiffTime, UTCTime)
import Data.Time.Clock.POSIX
import System.IO
import System.IO.Error (isEOFError)

-- NOTES:
-- 1. Currently, the queue is not bounded. If there's no consumer
--    it will keep growing and blow up memory. A solution could be
--    a bounded queue, which will be flushed when trying to write
--    to a full queue.
-- 2. The log lines are tagged by timestamp only, so if two nodes
--    emit at the exact same microsecond, there's evidence lost.
--    The tag could be a tuple of timestamp and filepath hash to avoid that.
--    For later processing, the fully parsed line provides the "host"
--    field for proper labelling.
-- 3. Possibly correlate the polling delay (currently hardcoded 25ms) to the
--    deltaT cutoff in the thread which processes the in-buffer.

data Ingestor = Ingestor
  { ingInBuffer :: !(TVar (Map.Map UTCTime ByteString))
  , ingOutQueue :: !(TQueue ByteString)
  }

newtype Timestamp = Timestamp UTCTime

instance FromJSON Timestamp where
  parseJSON = withObject "Timestamp" $ \o ->
    Timestamp <$> o .: "at"

-- The interval in ms for which ingested lines will remain
-- buffered, before being piped to the queue for consumption.
-- Any consumer will have that as "lag behind" to real-time.
mkIngestor :: Int -> IO Ingestor
mkIngestor millisecs = do
  ingestor <- atomically $
    Ingestor <$> newTVar Map.empty <*> newTQueue
  void . forkIO $
    go ingestor
  pure ingestor
  where
    deltaT :: NominalDiffTime
    deltaT = fromIntegral millisecs / 1000

    -- Process the in-buffer by removing everything older than the cutoff
    -- deltaT and writing it, sorted by timestamp, into the out-queue.
    go Ingestor{..} = forever $ do
      threadDelay $ millisecs * 1000
      now <- getPOSIXTime
      let cutoff = posixSecondsToUTCTime $ now - deltaT
      !m <- atomically $
        stateTVar ingInBuffer $
          Map.spanAntitone (< cutoff)
      atomically $
        mapM_ (writeTQueue ingOutQueue . snd) (Map.toAscList m)

-- Blocking read
readLineIngestor :: Ingestor -> IO ByteString
readLineIngestor = atomically . readTQueue . ingOutQueue

ingestFileThreaded :: Ingestor -> FilePath -> IO ()
ingestFileThreaded Ingestor{ingInBuffer} fp =
  void . forkIO $
    -- The ingestion thread may silently die
    handle (\SomeException{} -> pure ())
      thread
  where
    thread = withFile fp ReadMode $ \hdl -> do
      -- Ingestion will start at the current end of file!
      hSeek hdl SeekFromEnd 0
      forever $ do
        threadDelay $ 25 * 1000

        -- This whole polling logic exists to avoid lazy I/O
        hasInput <- hasNewInput hdl
        when hasInput $
          ingestLines hdl

    -- Swallow EOF while polling for new input, rethrow anything else
    hasNewInput :: Handle -> IO Bool
    hasNewInput hdl = handle
      (\(err :: IOException) -> if isEOFError err then pure False else ioError err)
      (hReady hdl)

    ingestLines :: Handle -> IO ()
    ingestLines hdl = do
      line <- ByteString.hGetLine hdl
      -- There's no requirement for each and every line to be a trace event.
      -- While with the Haskell node this is almost always the case, it can't be
      -- a general assumption.
      -- If the line doesn't look like a timestamped JSON object, we skip it.
      forM_ (decodeStrict' line) $ \(Timestamp ts) ->
        atomically $ modifyTVar' ingInBuffer $
          Map.insert ts line

      hasInput <- hasNewInput hdl
      when hasInput $
        ingestLines hdl

{-
-- example usage:
_testRunConsumer :: IO ()
_testRunConsumer = do
  ing <- mkIngestor 1000
  ingestFileThreaded ing "log-small.txt"
  ingestFileThreaded ing "something-else.txt"
  forever $
    readLineIngestor ing >>= print
-}
