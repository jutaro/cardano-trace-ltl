{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Check                  (checkFormula)
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy
import           Cardano.Trace.Feed                 (read)

import           Prelude                            hiding (read)
import qualified Prelude

import           Cardano.Trace.Feed                 (Filename,
                                                     TemporalEventDurationMicrosec)
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

data Leadership = Check | Yes | No deriving (Show, Eq, Ord)

data Adoption = Forged | Adopted deriving (Show, Eq, Ord)

data CommonProps = CommonProps { slot :: Int } deriving (Show, Generic)

instance FromJSON CommonProps

instance Finite Leadership where
  elements = Set.fromList [Check, Yes, No]

instance Finite Adoption where
  elements = Set.fromList [Forged, Adopted]

leadershipFindByTy :: [TraceMessage] -> Leadership -> Maybe TraceMessage
leadershipFindByTy msgs Check = find (\msg -> tmsgNS msg == "Forge.Loop.StartLeadershipCheck") msgs
leadershipFindByTy msgs No = find (\msg -> tmsgNS msg == "Forge.Loop.NodeNotLeader") msgs
leadershipFindByTy msgs Yes = find (\msg -> tmsgNS msg == "Forge.Loop.NodeIsLeader") msgs

adoptionFindByTy :: [TraceMessage] -> Adoption -> Maybe TraceMessage
adoptionFindByTy msgs Forged = find (\msg -> tmsgNS msg == "Forge.Loop.ForgedBlock") msgs
adoptionFindByTy msgs Adopted = find (\msg -> tmsgNS msg == "Forge.Loop.AdoptedBlock") msgs

instance Event [TraceMessage] Leadership where
  ty msgs t = isJust $ leadershipFindByTy msgs t

  props msgs t =
    case leadershipFindByTy msgs t of
      Just x ->
        case fromJSON (Object (tmsgData x)) of
          Success (CommonProps slot) ->
            singleton "slot" (IntValue slot)
          Error err -> error (err <> " for " <> show (tmsgData x) <> " and " <> show t)
      Nothing -> error "impossible"

instance Event [TraceMessage] Adoption where
  ty msgs t = isJust $ adoptionFindByTy msgs t

  props msgs t =
    case adoptionFindByTy msgs t of
      Just x ->
        case fromJSON (Object (tmsgData x)) of
          Success (CommonProps slot) ->
            singleton "slot" (IntValue slot)
          Error err -> error (err <> " for " <> show (tmsgData x) <> " and " <> show t)
      Nothing -> error "impossible"

-- ☐ (∀i. Check("slot" = i) ⇒ ◯(1ms) (Yes("slot" = i) ∨ No("slot" = i)))
prop1 :: TemporalEventDurationMicrosec -> Formula Leadership
prop1 dur = Forall $ PropForall "i" $
  Implies
    (PropAtom Check (fromList [PropConstraint "slot" (Var "i")]))
    (RepeatNext False (floor (1000 / fromIntegral dur))
      (Or
         [
           PropAtom Yes (fromList [PropConstraint "slot" (Var "i")])
         ,
           PropAtom No (fromList [PropConstraint "slot" (Var "i")])
         ]
      )
    )

-- ∀i. ¬ (Success("slot" = i) ∨ Failure("slot" = i)) U˜ Start("slot" = i)
prop2 :: Formula Leadership
prop2 = PropForall "i" $ Until
  True
  (Not $
    Or
      [
        PropAtom Yes (fromList [PropConstraint "slot" (Var "i")])
      ,
        PropAtom No (fromList [PropConstraint "slot" (Var "i")])
      ]
  )
  (PropAtom Check (fromList [PropConstraint "slot" (Var "i")]))

-- ☐ (∀i. ForgedBlock("slot" = i) ⇒ ♢ AdoptedBlock("slot" = i))
prop3 :: Formula Adoption
prop3 = Forall $ PropForall "i" $ Implies
  (PropAtom Forged (fromList [PropConstraint "slot" (Var "i")]))
  (Exists (PropAtom Adopted (fromList [PropConstraint "slot" (Var "i")])))

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
