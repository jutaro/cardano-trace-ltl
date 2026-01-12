module Cardano.Trace.Feed

import Cardano.Logging.Types.TraceMessage
import Data.List
import Data.String
import System.File.ReadWrite
import System

Filename : Type
Filename = String

data Quadruple a b c d 
  = MkQuadruple a b c d

TemporalEvent : Type
TemporalEvent = (List TraceMessage, Int)

TemporalEventDurationMicrosec : Type
TemporalEventDurationMicrosec = Int

fill : Int
  -> TemporalEventDurationMicrosec 
  -> List TraceMessage 
  -> Int 
  -> List TraceMessage 
  -> Quadruple TemporalEvent Int (List TraceMessage) Int
fill idx duration acc t (x :: xs) =
  if tmsgAt x <= (t + duration) then
    fill idx duration (x :: acc) t xs
  else
    MkQuadruple (reverse acc, idx) (t + duration) (x :: xs) (idx + 1)
fill idx duration acc t [] = 
  MkQuadruple (reverse acc, idx) (t + duration) [] (idx + 1)

slice : TemporalEventDurationMicrosec -> List TraceMessage -> List TemporalEvent
slice duration [] = []
slice duration msg@(x :: _) = go 0 (tmsgAt x) msg where
  go : Int -> Int -> List TraceMessage -> List TemporalEvent
  go _ _ [] = []
  go idx t msgs =
    let MkQuadruple e t' msg' idx' = fill idx duration [] t msgs in
    e :: go idx' t' msg'

sortByTimestamp : List TraceMessage -> List TraceMessage
sortByTimestamp = sortBy (\x, y => compare (tmsgAt x) (tmsgAt y))

decodeOrFail : Either String a -> IO a
decodeOrFail (Right x) = pure x
decodeOrFail (Left err) = die err

read : Filename -> TemporalEventDurationMicrosec -> IO (List TemporalEvent)
read filename duration = do
  case !(readFile filename) of 
    Left err => die ("Failed to read file: " ++ show err)
    Right contents => do 
      let traces = lines contents
      msgs <- traverse (decodeOrFail . decodeTraceMessage) traces
      let events = slice duration (sortByTimestamp msgs)
      pure events
