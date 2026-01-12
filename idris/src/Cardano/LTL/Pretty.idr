module Cardano.LTL.Pretty

import Cardano.LTL.Lang.Formula
import Data.List
import Data.SortedSet as Set

%default covering

data Lvl = Z | O 

Eq Lvl where
  Z == Z = True
  O == O = True
  _ == _ = False

Ord Lvl where
  compare Z Z = EQ
  compare Z O = LT
  compare O Z = GT
  compare O O = EQ

surround : Lvl -> Lvl -> String -> String
surround outer inner str = if outer <= inner then str else "(" ++ str ++ ")"

weak : Bool -> String -> String
weak True x = x ++ "˜"
weak False x = x

intercalateStr : String -> List String -> String
intercalateStr _ [] = ""
intercalateStr sep (x :: xs) = foldl (\acc, y => acc ++ sep ++ y) x xs

prettyPropValue : PropValue -> String
prettyPropValue (IntValue i) = show i
prettyPropValue (TextValue x) = x

prettyPropKeyValueList : List (PropName, PropValue) -> String
prettyPropKeyValueList = intercalateStr "\n" . map go where
  go : (PropName, PropValue) -> String
  go (n, v) = show n ++ " = " ++ prettyPropValue v

prettyPropTerm : PropTerm -> String
prettyPropTerm (Var x) = x
prettyPropTerm (Const idx) = prettyPropValue idx

prettyPropConstraint : PropConstraint -> String
prettyPropConstraint (MkPropConstraint k v) = show k ++ " = " ++ prettyPropTerm v

prettyPropConstraints : List PropConstraint -> String
prettyPropConstraints = intercalateStr ", " . map prettyPropConstraint

prettyFormula : Show a => Formula a -> Lvl -> String
prettyFormula (Forall phi) lvl = surround lvl Z $ "☐ " ++ prettyFormula phi O
prettyFormula (Exists phi) lvl = surround lvl Z $ "♢ " ++ prettyFormula phi O
prettyFormula (Next w phi) lvl = surround lvl Z $ weak w "◯" ++ " " ++ prettyFormula phi O
prettyFormula (RepeatNext w k phi) lvl = surround lvl Z $ weak w "◯" ++ "(" ++ show k ++ ") " ++ prettyFormula phi O
prettyFormula (Until w phi psi) lvl = surround lvl Z $ prettyFormula phi O ++ " " ++ weak w "|" ++ " " ++ prettyFormula psi O
prettyFormula (Implies phi psi) lvl = surround lvl Z $ prettyFormula phi O ++ " ⇒ " ++ prettyFormula psi O
prettyFormula (Or phis) lvl = surround lvl Z $ "(∨)" ++ foldl (\acc, x => acc ++ " " ++ prettyFormula x O) "" phis
prettyFormula (And phis) lvl = surround lvl Z $ "(∧)" ++ foldl (\acc, x => acc ++ " " ++ prettyFormula x O) "" phis
prettyFormula (Not phi) lvl = surround lvl Z $ "¬ " ++ prettyFormula phi O
prettyFormula Top lvl = surround lvl O "⊤"
prettyFormula Bottom lvl = surround lvl O "⊥"
prettyFormula (PropForall x phi) lvl = surround lvl Z $ "∀" ++ x ++ ". " ++ prettyFormula phi Z
prettyFormula (PropAtom c is) lvl = surround lvl O $ show c ++ "(" ++ prettyPropConstraints (Set.toList is) ++ ")"
prettyFormula (PropEq _ t v) lvl = surround lvl Z $ prettyPropTerm t ++ " = " ++ prettyPropValue v
