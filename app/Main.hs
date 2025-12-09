{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Check                  (checkFormula)
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Satisfy
import           Cardano.Trace.Feed                 (read)

import           Prelude                            hiding (read)
import qualified Prelude

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

data Leadership = Check | Yes | No deriving (Show, Eq, Ord)

data LeadershipProps = LeadershipProps { slot :: Int } deriving (Show, Generic)

instance FromJSON LeadershipProps

instance Finite Leadership where
  elements = Set.fromList [Check, Yes, No]

findByTy :: [TraceMessage] -> Leadership -> Maybe TraceMessage
findByTy msgs Check = find (\msg -> tmsgNS msg == "Forge.Loop.StartLeadershipCheck") msgs
findByTy msgs No = find (\msg -> tmsgNS msg == "Forge.Loop.NodeNotLeader") msgs
findByTy msgs Yes = find (\msg -> tmsgNS msg == "Forge.Loop.NodeIsLeader") msgs


instance Event [TraceMessage] Leadership where
  ty msgs t = isJust $ findByTy msgs t

  props msgs t =
    case findByTy msgs t of
      Just x ->
        case fromJSON (Object (tmsgData x)) of
          Success (LeadershipProps slot) ->
            singleton "slot" (IntValue slot)
          Error err -> error (err <> " for " <> show (tmsgData x) <> " and " <> show t)
      Nothing -> error "impossible"

-- ☐ (∀i. Check("slot" = i) ⇒ ◯(1ms) (Yes("slot" = i) ∨ No("slot" = i)))
prop1 :: Formula Leadership
prop1 = Forall $ PropForall "i" $
  Implies
    (PropAtom Check (fromList [PropConstraint "slot" (Var "i")]))
    (RepeatNext False 4
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

main :: IO ()
main = do
  events <- read "log-small.txt"
  -- for_ events $ \e ->
  --   print e
  -- print (checkFormula mempty prop1)
  putStrLn "------------------------"
  -- print (satisfies prop1 events)
  print (satisfies prop2 events)
