{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

module Main(main) where

import           Cardano.LTL.Check        (Error (..), checkFormula)
import           Cardano.LTL.Lang.Formula
import qualified Cardano.LTL.Prec         as Prec
import           Cardano.LTL.Pretty       (prettyFormula)
import           Cardano.LTL.Satisfy      (SatisfactionResult (..), satisfies)
import           Data.Map                 (singleton)
import           Data.Set                 (fromList)
import           Data.Text                (unpack)
import           Test.Tasty
import           Test.Tasty.HUnit

type Identifier = EventIndex

data Ty = Start | Success | Failure deriving (Show, Eq, Ord)

data Msg = Msg Ty Identifier | Placeholder deriving (Show, Eq, Ord)

instance Event Msg Ty where
  ofTy (Msg t _) t'  = t == t'
  ofTy Placeholder _ = False

  index (Msg _ i)   = i
  index Placeholder = 999

  props (Msg _ i) _ = singleton "idx" (IntValue (fromIntegral i))

  beg _ = 0

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

-- ∀i. ☐ (Start("idx" = i) ⇒ ♢² (Success("idx" = i) ∨ Failure("idx" = i)))
-- Start must be followed by either a corresponding success or failure within 3 units of time.
prop1 :: Formula Ty
prop1 = PropForall "i" $ Forall 0 $
  Implies
    (PropAtom Start (fromList [PropConstraint "idx" (Var "i")]))
    (ExistsN 3 $
      Or
        (PropAtom Success (fromList [PropConstraint "idx" (Var "i")]))
        (PropAtom Failure (fromList [PropConstraint "idx" (Var "i")]))

    )

-- ∀i. ¬ (Success("idx" = i) ∨ Failure("idx" = i)) |˜¹⁰⁰ Start("idx" = i)
-- Start mustn't be preceded by a corresponding success or failure.
prop2 :: Formula Ty
prop2 = PropForall "i" $ UntilN
  100
  (Not $
    Or
      (PropAtom Success (fromList [PropConstraint "idx" (Var "i")]))
      (PropAtom Failure (fromList [PropConstraint "idx" (Var "i")]))
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
    testCase (unpack $ prettyFormula syn1 Prec.Universe <> " is syntactically valid") $
      [] @?= checkFormula mempty syn1
  ,
    testCase (unpack $ prettyFormula syn2 Prec.Universe <> " is syntactically invalid") $
      [UnboundPropVarIdentifier "j"] @?= checkFormula mempty syn2
  ]

prop1SatisfiabilityTests :: TestTree
prop1SatisfiabilityTests = testGroup ("Satisfiability of: " <> unpack (prettyFormula prop1 Prec.Universe))
  [ testCase (show log1 <> " satisfies the formula") $
      satisfies prop1 log1 @?= Satisfied
  , testCase (show log2 <> " satisfies the formula") $
      satisfies prop1 log2 @?= Satisfied
  , testCase (show log3 <> " satisfies the formula") $
      satisfies prop1 log3 @?= Satisfied
  , testCase (show log4 <> " does not satisfy the formula") $
      satisfies prop1 log4 @?= Unsatisfied
        (fromList [(2, Start)])
  , testCase (show log5 <> " satisfies the formula") $
      satisfies prop1 log5 @?= Satisfied
  , testCase (show log6 <> " satisfies the formula") $
      satisfies prop1 log6 @?= Unsatisfied
        (fromList [(4,Start),(7,Success)])
  , testCase (show log7 <> " does not satisfy the formula") $
      satisfies prop1 log7 @?= Unsatisfied
        (fromList [(2, Start)])
  ]

prop2SatisfiabilityTests :: TestTree
prop2SatisfiabilityTests = testGroup ("Satisfiability of: " <> unpack (prettyFormula prop2 Prec.Universe))
  [
    testCase (show log1 <> " satisfies the formula") $
      satisfies prop2 log1 @?= Satisfied
  , testCase (show log5 <> " satisfies the formula") $
      satisfies prop2 log5 @?= Satisfied
  , testCase (show logEmpty <> " satisfies the formula") $
      satisfies prop2 logEmpty @?= Satisfied
  , testCase (show log8 <> "does not satisfy the formula") $
      satisfies prop2 log8 @?= Unsatisfied
        (fromList [(1,Start),(1,Success)])
  , testCase (show log9 <> " does not satisfy the formula") $
      satisfies prop2 log9 @?= Unsatisfied
        (fromList [(1,Success)])
  , testCase (show log10 <> " satisfies the formula") $
      satisfies prop2 log10 @?= Satisfied
  , testCase (show log11 <> " does not satisfy the formula") $
      satisfies prop2 log11 @?=
      Unsatisfied
        (fromList [(1,Start),(1,Success),(2,Success)])

  ]
