module Unit

import Cardano.LTL.Check
import Cardano.LTL.Lang.Formula
import Cardano.LTL.Pretty
import Cardano.LTL.Satisfy
import Data.SortedMap as Map
import Data.SortedSet as Set
import Data.String
import System

singletonMap : Ord k => k -> v -> Map.SortedMap k v
singletonMap k v = Map.insert k v Map.empty

assertEq : (Eq a, Show a) => String -> a -> a -> IO Bool
assertEq label expected actual =
  if expected == actual then
    putStrLn (label ++ " OK") >> pure True
  else
    putStrLn (label ++ " FAIL\n  expected: " ++ show expected ++ "\n  actual: " ++ show actual) >> pure False

data Ty = Start | Success | Failure deriving (Show, Eq, Ord)

data Msg = Msg Ty Int | Placeholder deriving (Show, Eq, Ord)

implementation Event Msg Ty where
  ofTy (Msg t _) t' = t == t'
  ofTy Placeholder _ = False

  index (Msg _ i) = i
  index Placeholder = -1

  props (Msg _ i) _ = singletonMap (MkPropName "idx") (IntValue i)
  props Placeholder _ = Map.empty

log1 : List Msg
log1 = [Msg Start 2, Placeholder, Msg Success 2]

log2 : List Msg
log2 = [Msg Start 1, Placeholder, Msg Failure 1, Placeholder]

log3 : List Msg
log3 = [Placeholder]

log4 : List Msg
log4 = [Msg Start 2, Placeholder]

log5 : List Msg
log5 = [ Msg Start 1
       , Placeholder
       , Msg Failure 1
       , Placeholder
       , Msg Start 4
       , Placeholder
       , Msg Success 4
       , Placeholder
       ]

log6 : List Msg
log6 = [ Msg Start 1
       , Placeholder
       , Msg Failure 1
       , Placeholder
       , Msg Start 4
       , Placeholder
       , Msg Success 7
       , Placeholder
       ]

log7 : List Msg
log7 = [Msg Start 2, Placeholder, Placeholder, Msg Failure 2]

log8 : List Msg
log8 =
  [ Placeholder
  , Msg Success 1
  , Placeholder
  , Msg Start 1
  , Placeholder
  , Placeholder
  ]

log9 : List Msg
log9 =
  [ Placeholder
  , Msg Success 1
  , Placeholder
  , Placeholder
  ]

log10 : List Msg
log10 =
  [ Msg Start 1
  , Msg Success 1
  , Msg Start 2
  , Msg Success 2
  ]

log11 : List Msg
log11 =
  [ Msg Start 1
  , Msg Success 1
  , Msg Start 1
  , Msg Success 2
  ]

logEmpty : List Msg
logEmpty = []

prop1 : Formula Ty
prop1 = PropForall "i" $ Forall $
  Implies
    (PropAtom Start (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")]))
    (RepeatNext False 2
      (Or
        [ PropAtom Success (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")])
        , PropAtom Failure (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")])
        ]
      )
    )

prop2 : Formula Ty
prop2 = PropForall "i" $ Until True
  (Not $
    Or
      [ PropAtom Success (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")])
      , PropAtom Failure (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")])
      ]
  )
  (PropAtom Start (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")]))

syn1 : Formula ()
syn1 = PropForall "i" (PropAtom () (Set.fromList [PropConstraint (MkPropName "idx") (Var "i")]))

syn2 : Formula ()
syn2 = PropForall "i" (PropAtom () (Set.fromList [PropConstraint (MkPropName "idx") (Var "j")]))

runTests : IO Bool
runTests = do
  ok1 <- assertEq "syntactic valid" [] (checkFormula Set.empty syn1)
  ok2 <- assertEq "syntactic invalid" [UnboundPropVarIdentifier "j"] (checkFormula Set.empty syn2)
  ok3 <- assertEq "log1 satisfies prop1" Satisfied (satisfies prop1 log1)
  ok4 <- assertEq "log2 satisfies prop1" Satisfied (satisfies prop1 log2)
  ok5 <- assertEq "log3 satisfies prop1" Satisfied (satisfies prop1 log3)
  ok6 <- assertEq "log4 fails prop1"
    (Unsatisfied (PropForall "i" (Not (PropEq (Set.fromList [2]) (Var "i") (IntValue 2)))) (Set.fromList [2]))
    (satisfies prop1 log4)
  ok7 <- assertEq "log5 satisfies prop1" Satisfied (satisfies prop1 log5)
  ok8 <- assertEq "log6 fails prop1"
    (Unsatisfied
      (PropForall "i"
        (Implies
          (PropEq (Set.fromList [4]) (Var "i") (IntValue 4))
          (PropEq (Set.fromList [7]) (Var "i") (IntValue 7))
        )
      )
      (Set.fromList [4, 7])
    )
    (satisfies prop1 log6)
  ok9 <- assertEq "log7 fails prop1"
    (Unsatisfied (PropForall "i" (Not (PropEq (Set.fromList [2]) (Var "i") (IntValue 2)))) (Set.fromList [2]))
    (satisfies prop1 log7)
  ok10 <- assertEq "log1 satisfies prop2" Satisfied (satisfies prop2 log1)
  ok11 <- assertEq "log5 satisfies prop2" Satisfied (satisfies prop2 log5)
  ok12 <- assertEq "logEmpty satisfies prop2" Satisfied (satisfies prop2 logEmpty)
  ok13 <- assertEq "log8 fails prop2"
    (Unsatisfied (PropForall "i" (Not (PropEq (Set.fromList [1]) (Var "i") (IntValue 1)))) (Set.fromList [1]))
    (satisfies prop2 log8)
  ok14 <- assertEq "log9 fails prop2"
    (Unsatisfied (PropForall "i" (Not (PropEq (Set.fromList [1]) (Var "i") (IntValue 1)))) (Set.fromList [1]))
    (satisfies prop2 log9)
  ok15 <- assertEq "log10 satisfies prop2" Satisfied (satisfies prop2 log10)
  ok16 <- assertEq "log11 fails prop2"
    (Unsatisfied
      (PropForall "i"
        (Or
          [ PropEq (Set.fromList [1]) (Var "i") (IntValue 1)
          , And
              [ Not (PropEq (Set.fromList [1]) (Var "i") (IntValue 1))
              , And
                  [ Not (PropEq (Set.fromList [1]) (Var "i") (IntValue 1))
                  , Or
                      [ PropEq (Set.fromList [1]) (Var "i") (IntValue 1)
                      , And
                          [ Not (PropEq (Set.fromList [1]) (Var "i") (IntValue 1))
                          , Not (PropEq (Set.fromList [2]) (Var "i") (IntValue 2))
                          ]
                      ]
                  ]
              ]
          ]
        )
      )
      (Set.fromList [1, 2])
    )
    (satisfies prop2 log11)
  pure (and [ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16])

main : IO ()
main = do
  ok <- runTests
  if ok then
    putStrLn "All tests passed"
  else
    exitFailure
