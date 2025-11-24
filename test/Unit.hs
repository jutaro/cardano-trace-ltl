{-# LANGUAGE MultiParamTypeClasses #-}
module Main(main) where

import           Cardano.LTL.Check   (Error (..), checkFormula)
import           Cardano.LTL.Lang
import           Cardano.LTL.Pretty  (Lvl (Z), prettyFormula)
import           Cardano.LTL.Satisfy (SatisfactionResult (..), satisfies)
import           Data.Map            (singleton)
import           Data.Set            (fromList)
import           Test.Tasty
import           Test.Tasty.HUnit

type Identifier = Int

data Ty = Start | Success | Failure | Placeholder deriving (Show, Eq)

data Msg = Msg Ty Identifier deriving (Show, Eq)

instance Event Msg Ty where
  ty (Msg e _) = e
  props (Msg _ i) = singleton "idx" (IntValue i)

log1 :: [Msg]
log1 = [Msg Start 2, Msg Placeholder (-1), Msg Success 2]

log2 :: [Msg]
log2 = [Msg Start 1, Msg Placeholder (-1), Msg Failure 1, Msg Placeholder 2]

log3 :: [Msg]
log3 = [Msg Placeholder 0]

log4 :: [Msg]
log4 = [Msg Start 2, Msg Placeholder 0]

log5 :: [Msg]
log5 = [ Msg Start 1
       , Msg Placeholder (-1)
       , Msg Failure 1
       , Msg Placeholder 2
       , Msg Start 4
       , Msg Placeholder (-1)
       , Msg Success 4
       , Msg Placeholder 2
       ]

log6 :: [Msg]
log6 = [ Msg Start 1
       , Msg Placeholder (-1)
       , Msg Failure 1
       , Msg Placeholder 2
       , Msg Start 4
       , Msg Placeholder (-1)
       , Msg Success 7
       , Msg Placeholder 2
       ]

log7 :: [Msg]
log7 = [Msg Start 2, Msg Placeholder 0, Msg Placeholder 0, Msg Failure 2]

log8 :: [Msg]
log8 =
  [
    Msg Placeholder 0
  , Msg Success 1
  , Msg Placeholder 0
  , Msg Start 1
  , Msg Placeholder 0
  , Msg Placeholder 0
  ]

log9 :: [Msg]
log9 =
  [
    Msg Placeholder 0
  , Msg Success 1
  , Msg Placeholder 0
  , Msg Placeholder 0
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
    testCase (prettyFormula syn1 Z <> " is syntactically valid") $
      [] @?= checkFormula mempty syn1
  ,
    testCase (prettyFormula syn2 Z <> " is syntactically invalid") $
      [UnboundPropVarIdentifier "j"] @?= checkFormula mempty syn2
  ]

prop1SatisfiabilityTests :: TestTree
prop1SatisfiabilityTests = testGroup ("Satisfiability of: " <> prettyFormula prop1 Z)
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
prop2SatisfiabilityTests = testGroup ("Satisfiability of: " <> prettyFormula prop2 Z)
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
