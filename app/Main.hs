{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import           Cardano.LTL.Check (checkFormula)
import           Cardano.LTL.Lang
import           Cardano.LTL.Satisfy
import           Cardano.Trace.Feed (read)

import           Prelude hiding (read)
import qualified Prelude

import           Control.Monad (unless)
import           Data.Foldable (for_)
import           Data.List (find)
import           Data.Map (singleton)
import           Data.Maybe (isJust)
import           Data.Set (fromList)
import           Data.Text (unpack)

type Identifier = Int

data Ty = Start | Success | Failure | Placeholder deriving (Show, Eq)

data Msg = Msg Ty Identifier deriving Show

instance Event Msg Ty where
  ty (Msg e _) = e
  props (Msg _ i) = singleton "idx" (IntValue i)

logEmpty :: [Msg]
logEmpty = []

log1Ok :: [Msg]
log1Ok = [Msg Start 2, Msg Placeholder (-1), Msg Success 2]

log2Ok :: [Msg]
log2Ok = [Msg Start 1, Msg Placeholder (-1), Msg Failure 1, Msg Placeholder 2]

log3Ok :: [Msg]
log3Ok = [Msg Placeholder 0]

log4NotOk :: [Msg]
log4NotOk = [Msg Start 2, Msg Placeholder 0]

log5Ok :: [Msg]
log5Ok = [ Msg Start 1
         , Msg Placeholder (-1)
         , Msg Failure 1
         , Msg Placeholder 2
         , Msg Start 4
         , Msg Placeholder (-1)
         , Msg Success 4
         , Msg Placeholder 2
         ]

log6NotOk :: [Msg]
log6NotOk = [ Msg Start 1
            , Msg Placeholder (-1)
            , Msg Failure 1
            , Msg Placeholder 2
            , Msg Start 4
            , Msg Placeholder (-1)
            , Msg Success 7
            , Msg Placeholder 2
            ]

log7 :: [Msg]
log7 =
  [
    Msg Success 1
  , Msg Start 1
  ]

log8 :: [Msg]
log8 =
  [
    Msg Success 1
  ]

data Leadership = Check | Yes | No | Irrelevant deriving (Show, Eq)

-- Forge.Loop.StartLeadershipCheck
-- Forge.Loop.NodeNotLeader
-- Forge.Loop.NodeIsLeader

instance Event [TraceMessage] Leadership where
  ty msgs =
    if | isJust $ find (\msg -> tmsgNS msg == "Forge.Loop.StartLeadershipCheck") msgs -> Check
       | isJust $ find (\msg -> tmsgNS msg == "Forge.Loop.NodeNotLeader") msgs        -> No
       | isJust $ find (\msg -> tmsgNS msg == "Forge.Loop.NodeIsLeader") msgs         -> Yes
       | otherwise                                                                    -> Irrelevant
  props [] = mempty
  props (msg : _) = singleton "thread" (IntValue (Prelude.read $ unpack $ tmsgThread msg))

-- ☐ (Check ⇒ ◯(10ms) (Yes ∨ No))
prop0 :: Formula Leadership
prop0 = Forall $
  Implies
    (PropAtom Check (fromList []))
    (RepeatNext False 100
      (Or
         [
           PropAtom Yes (fromList [])
         ,
           PropAtom No (fromList [])
         ]
      )
    )

-- ∀i. ☐ (Check("thread" = i) ⇒ ◯(10ms) (Yes("thread" = i) ∨ No("thread" = i)))
prop1 :: Formula Leadership
prop1 = PropForall "i" $ Forall $
  Implies
    (PropAtom Check (fromList [PropConstraint "thread" (Var "i")]))
    (RepeatNext False 100
      (Or
         [
           PropAtom Yes (fromList [PropConstraint "thread" (Var "i")])
         ,
           PropAtom No (fromList [PropConstraint "thread" (Var "i")])
         ]
      )
    )

main :: IO ()
main = do
  events <- read "log.txt"
  -- for_ events $ \e ->
  --   print e
  -- print (checkFormula mempty prop1)
  putStrLn "------------------------"
  print (satisfies prop0 events)
  -- print (satisfies prop1 log2Ok)
  -- print (satisfies prop1 log3Ok)
  -- print (satisfies prop1 log4NotOk)
  -- print (satisfies prop1 log5Ok)
  -- print (satisfies prop1 log6NotOk)
  --
  -- print (satisfies prop2 log1Ok)
  -- print (satisfies prop2 logEmpty)
  -- print (satisfies prop2 log4NotOk)
  -- print (satisfies prop2 log7)
  -- print (satisfies prop2 log8)
