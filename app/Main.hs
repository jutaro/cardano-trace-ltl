module Main(main) where

import           Cardano.LTL.Check   (checkFormula)
import           Cardano.LTL.Lang
import           Cardano.LTL.Satisfy
import           Data.Map            (singleton)
import           Data.Set            (fromList)

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

-- ∀i. ☐ (Start("idx" = i) ⇒ ◯(5) (Success("idx" = i) ∨ Failure("idx" = i)))
prop1 :: Formula Ty
prop1 = PropForall "i" $ Forall $
  Implies
    (PropAtom Start (fromList [PropConstraint "idx" (Var "i")]))
    (RepeatNext False 5
      (Or
         [
           PropAtom Success (fromList [PropConstraint "idx" (Var "i")])
         ,
           PropAtom Failure (fromList [PropConstraint "idx" (Var "i")])
         ]
      )
    )

-- ∀i. ¬ (Success("idx" = i) ∨ Failure("idx" = i)) U˜ Start("idx" = i)
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
main = do
  print (checkFormula mempty prop1)
  print (satisfies prop1 log1Ok)
  print (satisfies prop1 log2Ok)
  print (satisfies prop1 log3Ok)
  print (satisfies prop1 log4NotOk)
  print (satisfies prop1 log5Ok)
  print (satisfies prop1 log6NotOk)

  print (satisfies prop2 log1Ok)
  print (satisfies prop2 logEmpty)
  print (satisfies prop2 log4NotOk)
  print (satisfies prop2 log7)
  print (satisfies prop2 log8)
