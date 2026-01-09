{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Check                  (checkFormula)
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy

import           Prelude                            hiding (read)
import qualified Prelude

import           Cardano.LTL.Pretty                 (Lvl (Z), prettyFormula,
                                                     prettyPropKeyValueList)
import           Cardano.Trace.Feed                 (Filename, TemporalEvent,
                                                     TemporalEventDurationMicrosec,
                                                     read)
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

newtype TraceProps = TraceProps { slot :: Int } deriving (Show, Eq, Ord, Generic)

instance FromJSON TraceProps

deriving instance Eq TraceMessage

deriving instance Ord TraceMessage

instance Event TemporalEvent Text where
  ofTy (msgs, _) c = isJust $ find (\msg -> tmsgNS msg == c) msgs
  index (_, idx) = idx
  props (msgs, _) c =
    case find (\msg -> tmsgNS msg == c) msgs of
      Just x ->
        case fromJSON (Object (tmsgData x)) of
          Error err                 -> error ("json parsing error " <> err)
          Success (TraceProps slot) -> singleton "slot" (IntValue slot)
      Nothing -> error ("Not an event of type " <> unpack c)

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
prettyTemporalEvent (msgs, _) = intercalate "\n" (fmap prettyTraceMessage msgs)

prettySatisfactionResult :: [TemporalEvent] -> Formula Text -> SatisfactionResult Text -> Text
prettySatisfactionResult events initial Satisfied = prettyFormula initial Z <> " " <> green "(✔)"
prettySatisfactionResult events initial (Unsatisfied phi rel) =
  prettyFormula initial Z <> " ⇔ " <> prettyFormula phi Z <> " " <> red "(✗)" <> "\n"
    <> tabulate 2 (intercalate "\n------\n" (go (Set.toList rel))) where
      -- go :: [Int] -> [Text]
      -- go = fmap (pack . show)
      go []       = []
      go (e : es) = prettyTemporalEvent (events !! e) : go es

check :: Formula Text -> [TemporalEvent] -> IO ()
check phi events =
  putStrLn (unpack $ prettySatisfactionResult events phi (satisfies phi events))

-- ☐ (∀i. StartLeadershipCheck("slot" = i) ⇒ ◯(1ms) (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)))
prop1 :: TemporalEventDurationMicrosec -> Formula Text
prop1 dur = Forall $ PropForall "i" $
  Implies
    (PropAtom "Forge.Loop.StartLeadershipCheck" (fromList [PropConstraint "slot" (Var "i")]))
    (RepeatNext False (floor (1000 / fromIntegral dur))
      (Or
         [
           PropAtom "Forge.Loop.NodeIsLeader" (fromList [PropConstraint "slot" (Var "i")])
         ,
           PropAtom "Forge.Loop.NodeNotLeader" (fromList [PropConstraint "slot" (Var "i")])
         ]
      )
    )

-- ∀i. ¬ (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)) |˜ StartLeadershipCheck("slot" = i)
prop2 :: Formula Text
prop2 = PropForall "i" $ Until
  True
  (Not $
    Or
      [
        PropAtom "Forge.Loop.NodeIsLeader" (fromList [PropConstraint "slot" (Var "i")])
      ,
        PropAtom "Forge.Loop.NodeNotLeader" (fromList [PropConstraint "slot" (Var "i")])
      ]
  )
  (PropAtom "Forge.Loop.StartLeadershipCheck" (fromList [PropConstraint "slot" (Var "i")]))

-- ☐ (∀i. ForgedBlock("slot" = i) ⇒ ♢ AdoptedBlock("slot" = i))
prop3 :: Formula Text
prop3 = Forall $ PropForall "i" $ Implies
  (PropAtom "Forge.Loop.ForgedBlock" (fromList [PropConstraint "slot" (Var "i")]))
  (Exists (PropAtom "Forge.Loop.AdoptedBlock" (fromList [PropConstraint "slot" (Var "i")])))

readArgs :: [String] -> IO (Filename, TemporalEventDurationMicrosec)
readArgs [x, readMaybe -> Just dur] = pure (x, dur)
readArgs _                          = die "Usage: $ <filename> <duration>"

main :: IO ()
main = do
  (!filename, !dur) <- getArgs >>= readArgs
  events <- read filename 250
  -- check (prop1 dur) events
  check prop2 events
  -- check prop3 events
