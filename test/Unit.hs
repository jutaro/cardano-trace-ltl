{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

module Main(main) where

import           Cardano.LTL.Check        (Error (..), checkFormula)
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Pretty       (Lvl (Z), prettyFormula)
import           Cardano.LTL.Satisfy      (SatisfactionResult (..), satisfies)
import           Data.Map                 (singleton)
import           Data.Set                 (fromList)
import           Data.Text                (unpack)
import           Test.Tasty
import           Test.Tasty.HUnit

type Identifier = Int

data Ty = Start | Success | Failure deriving (Show, Eq, Ord)

data Msg = Msg Ty Identifier | Placeholder deriving (Show, Eq, Ord)

instance Finite Ty where
  elements = fromList [Start, Success, Failure]

instance Event Msg Ty where
  ty (Msg t _) t'  = t == t'
  ty Placeholder _ = False
  props (Msg _ i) _ = singleton "idx" (IntValue i)

log1 :: [Msg]
log1 = [Msg Start 2, Placeholder, Msg Success 2]

log2 :: [Msg]
log2 = [Msg Start 1, Placeholder, Msg Failure 1, Placeholder]

log3 :: [Msg]
log3 = [Placeholder]

log4 :: [Msg]
log4 = [Msg Start 2, Placeholder]

log5 :: [Msg]
log5 = [ Msg Start 1
       , Placeholder
       , Msg Failure 1
       , Placeholder
       , Msg Start 4
       , Placeholder
       , Msg Success 4
       , Placeholder
       ]

log6 :: [Msg]
log6 = [ Msg Start 1
       , Placeholder
       , Msg Failure 1
       , Placeholder
       , Msg Start 4
       , Placeholder
       , Msg Success 7
       , Placeholder
       ]

log7 :: [Msg]
log7 = [Msg Start 2, Placeholder, Placeholder, Msg Failure 2]

log8 :: [Msg]
log8 =
  [
    Placeholder
  , Msg Success 1
  , Placeholder
  , Msg Start 1
  , Placeholder
  , Placeholder
  ]

log9 :: [Msg]
log9 =
  [
    Placeholder
  , Msg Success 1
  , Placeholder
  , Placeholder
  ]

log10 :: [Msg]
log10 =
  [
    Msg Start 1
  , Msg Success 1
  , Msg Start 2
  , Msg Success 2
  ]

log11 :: [Msg]
log11 =
  [
    Msg Start 1
  , Msg Success 1
  , Msg Start 1
  , Msg Success 2
  ]

logEmpty :: [Msg]
logEmpty = []

-- ∀i. ☐ (Start("idx" = i) ⇒ ◯(2) (Success("idx" = i) ∨ Failure("idx" = i)))
-- Start must be followed by either a corresponding success or failure within 2 units of time.
prop1 :: Formula Ty
prop1 = PropForall "i" $ Forall $
  Implies
    (PropAtom Start (fromList [PropConstraint "idx" (Var "i")]))
    (RepeatNext False 2
      (Or
        [
          PropAtom Success (fromList [PropConstraint "idx" (Var "i")])
        ,
          PropAtom Failure (fromList [PropConstraint "idx" (Var "i")])
        ]
      )
    )

-- ∀i. ¬ (Success("idx" = i) ∨ Failure("idx" = i)) U˜ Start("idx" = i)
-- Start mustn't be preceded by a corresponding success or failure.
prop2 :: Formula Ty
prop2 = PropForall "i" $ Until
  True
  (Not $
    Or
      [
        PropAtom Success (fromList [PropConstraint "idx" (Var "i")])
      ,
        PropAtom Failure (fromList [PropConstraint "idx" (Var "i")])
      ]
  )
  (PropAtom Start (fromList [PropConstraint "idx" (Var "i")]))

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Unit tests" [syntacticTests, prop1SatisfiabilityTests, prop2SatisfiabilityTests]

syn1 = PropForall "i" (PropAtom () (fromList [PropConstraint "idx" (Var "i")]))
syn2 = PropForall "i" (PropAtom () (fromList [PropConstraint "idx" (Var "j")]))

syntacticTests :: TestTree
syntacticTests = testGroup "Syntanctic checks"
  [
    testCase (unpack $ prettyFormula syn1 Z <> " is syntactically valid") $
      [] @?= checkFormula mempty syn1
  ,
    testCase (unpack $ prettyFormula syn2 Z <> " is syntactically invalid") $
      [UnboundPropVarIdentifier "j"] @?= checkFormula mempty syn2
  ]

prop1SatisfiabilityTests :: TestTree
prop1SatisfiabilityTests = testGroup ("Satisfiability of: " <> unpack (prettyFormula prop1 Z))
  [ testCase (show log1 <> " satisfies the formula") $
      satisfies prop1 log1 @?= Satisfied
  , testCase (show log2 <> " satisfies the formula") $
      satisfies prop1 log2 @?= Satisfied
  , testCase (show log3 <> " satisfies the formula") $
      satisfies prop1 log3 @?= Satisfied
  , testCase (show log4 <> " does not satisfy the formula") $
      satisfies prop1 log4 @?= Unsatisfied [Msg Start 2]
  , testCase (show log5 <> " satisfies the formula") $
      satisfies prop1 log5 @?= Satisfied
  , testCase (show log6 <> " satisfies the formula") $
      satisfies prop1 log6 @?= Unsatisfied
        [Msg Start 1, Msg Failure 1, Msg Start 4, Msg Success 7]
  , testCase (show log7 <> " does not satisfy the formula") $
      satisfies prop1 log7 @?= Unsatisfied [Msg Start 2, Msg Failure 2]
  ]

prop2SatisfiabilityTests :: TestTree
prop2SatisfiabilityTests = testGroup ("Satisfiability of: " <> unpack (prettyFormula prop2 Z))
  [
    testCase (show log1 <> " satisfies the formula") $
      satisfies prop2 log1 @?= Satisfied
  , testCase (show log5 <> " satisfies the formula") $
      satisfies prop2 log5 @?= Satisfied
  , testCase (show logEmpty <> " satisfies the formula") $
      satisfies prop2 logEmpty @?= Satisfied
  , testCase (show log8 <> "does not satisfy the formula") $
      satisfies prop2 log8 @?= Unsatisfied [Msg Success 1, Msg Start 1]
  , testCase (show log9 <> " does not satisfy the formula") $
      satisfies prop2 log9 @?= Unsatisfied [Msg Success 1]
  , testCase (show log10 <> " satisfies the formula") $
      satisfies prop2 log10 @?= Satisfied
  , testCase (show log11 <> " does not satisfy the formula") $
      satisfies prop2 log11 @?= Unsatisfied
        [Msg Start 1, Msg Success 1, Msg Start 1, Msg Success 2]
  ]
