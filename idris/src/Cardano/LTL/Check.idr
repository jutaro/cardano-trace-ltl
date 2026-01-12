module Cardano.LTL.Check

import Cardano.LTL.Lang.Formula
import Data.List
import Data.SortedSet as Set

public export
data Error = UnboundPropVarIdentifier PropVarIdentifier 

checkParamVar : Set.SortedSet PropVarIdentifier -> PropVarIdentifier -> List Error
checkParamVar bound x = if Set.contains x bound then [] else [UnboundPropVarIdentifier x]

checkParamTerm : Set.SortedSet PropVarIdentifier -> PropTerm -> List Error
checkParamTerm bound (Var x) = checkParamVar bound x
checkParamTerm _ (Const _) = []

checkParamConstraint : Set.SortedSet PropVarIdentifier -> PropConstraint -> List Error
checkParamConstraint bound (MkPropConstraint _ t) = checkParamTerm bound t

checkFormula : Set.SortedSet PropVarIdentifier -> Formula ty -> List Error
checkFormula bound (Forall phi) = checkFormula bound phi
checkFormula bound (Exists phi) = checkFormula bound phi
checkFormula bound (And phis) = foldl (++) [] (map (checkFormula bound) phis)
checkFormula bound (Or phis) = foldl (++) [] (map (checkFormula bound) phis)
checkFormula bound (Not phi) = checkFormula bound phi
checkFormula _ Bottom = []
checkFormula _ Top = []
checkFormula bound (Next _ phi) = checkFormula bound phi
checkFormula bound (RepeatNext _ _ phi) = checkFormula bound phi
checkFormula bound (Implies phi psi) = checkFormula bound phi ++ checkFormula bound psi
checkFormula bound (Until _ phi psi) = checkFormula bound phi ++ checkFormula bound psi
checkFormula bound (PropForall x phi) = checkFormula (Set.insert x bound) phi
checkFormula bound (PropEq _ t _) = checkParamTerm bound t
checkFormula bound (PropAtom _ cs) = foldl (++) [] (map (checkParamConstraint bound) (Set.toList cs))
