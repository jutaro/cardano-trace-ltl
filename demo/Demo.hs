{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Check                  (checkFormula)
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy

import           Prelude                            hiding (read)
import qualified Prelude

import           Cardano.Trace.Feed                 (Filename,
                                                     TemporalEventDurationMicrosec,
                                                     read)
import           Control.Monad                      (unless)
import           Data.Aeson
import           Data.Foldable                      (for_)
import           Data.List                          (find)
import           Data.Map                           (singleton)
import           Data.Maybe                         (isJust)
import           Data.Set                           (fromList)
import qualified Data.Set                           as Set
import           Data.Text                          (Text, unpack)
import           GHC.Generics                       (Generic)
import           System.Environment                 (getArgs)
import           System.Exit                        (die)
import           Text.Read                          (readMaybe)

data Trace = StartLeadershipCheck | NodeIsLeader | NodeNotLeader | ForgedBlock | AdoptedBlock deriving (Show, Eq, Ord)

newtype TraceProps = TraceProps { slot :: Int } deriving (Show, Eq, Ord, Generic)

instance FromJSON TraceProps

instance Finite Trace where
  elements = Set.fromList [StartLeadershipCheck, NodeIsLeader, NodeNotLeader, ForgedBlock, AdoptedBlock]

findByTy :: [TraceMessage] -> Trace -> Maybe TraceMessage
findByTy msgs StartLeadershipCheck = find (\msg -> tmsgNS msg == "Forge.Loop.StartLeadershipCheck") msgs
findByTy msgs NodeNotLeader = find (\msg -> tmsgNS msg == "Forge.Loop.NodeNotLeader") msgs
findByTy msgs NodeIsLeader = find (\msg -> tmsgNS msg == "Forge.Loop.NodeIsLeader") msgs
findByTy msgs ForgedBlock = find (\msg -> tmsgNS msg == "Forge.Loop.ForgedBlock") msgs
findByTy msgs AdoptedBlock = find (\msg -> tmsgNS msg == "Forge.Loop.AdoptedBlock") msgs

instance Event [TraceMessage] Trace where
  ty msgs t = isJust $ findByTy msgs t

  props msgs t =
    case findByTy msgs t of
      Just x ->
        case fromJSON (Object (tmsgData x)) of
          Success (TraceProps slot) ->
            singleton "slot" (IntValue slot)
          Error err -> error (err <> " for " <> show (tmsgData x) <> " and " <> show t)
      Nothing -> error "impossible"

-- ☐ (∀i. StartLeadershipCheck("slot" = i) ⇒ ◯(1ms) (NoteIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)))
prop1 :: TemporalEventDurationMicrosec -> Formula Trace
prop1 dur = Forall $ PropForall "i" $
  Implies
    (PropAtom StartLeadershipCheck (fromList [PropConstraint "slot" (Var "i")]))
    (RepeatNext False (floor (1000 / fromIntegral dur))
      (Or
         [
           PropAtom NodeIsLeader (fromList [PropConstraint "slot" (Var "i")])
         ,
           PropAtom NodeNotLeader (fromList [PropConstraint "slot" (Var "i")])
         ]
      )
    )

-- ∀i. ¬ (NodeIsLeader("slot" = i) ∨ NodeNotLeader("slot" = i)) |˜ StartLeadershipCheck("slot" = i)
prop2 :: Formula Trace
prop2 = PropForall "i" $ Until
  True
  (Not $
    Or
      [
        PropAtom NodeIsLeader (fromList [PropConstraint "slot" (Var "i")])
      ,
        PropAtom NodeNotLeader (fromList [PropConstraint "slot" (Var "i")])
      ]
  )
  (PropAtom StartLeadershipCheck (fromList [PropConstraint "slot" (Var "i")]))

-- ☐ (∀i. ForgedBlock("slot" = i) ⇒ ♢ AdoptedBlock("slot" = i))
prop3 :: Formula Trace
prop3 = Forall $ PropForall "i" $ Implies
  (PropAtom ForgedBlock (fromList [PropConstraint "slot" (Var "i")]))
  (Exists (PropAtom AdoptedBlock (fromList [PropConstraint "slot" (Var "i")])))

readArgs :: [String] -> IO (Filename, TemporalEventDurationMicrosec)
readArgs [x, readMaybe -> Just dur] = pure (x, dur)
readArgs _                          = die "Usage: $ <filename> <duration>"

main :: IO ()
main = do
  (!filename, !dur) <- getArgs >>= readArgs
  events <- read filename 250
  print (satisfies (prop1 dur) events)
  print (satisfies prop2 events)
  print (satisfies prop3 events)
