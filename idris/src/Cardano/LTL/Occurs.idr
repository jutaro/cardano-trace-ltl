module Cardano.LTL.Occurs

import Cardano.LTL.Lang.Formula
import Data.List
import Data.SortedSet as Set

export
occursPropTerm : PropVarIdentifier -> PropTerm -> Bool
occursPropTerm _ (Const _) = False
occursPropTerm x (Var x') = x == x'

export
occursPropConstraint : PropVarIdentifier -> PropConstraint -> Bool
occursPropConstraint x (MkPropConstraint _ t) = occursPropTerm x t

export
occursFormula : PropVarIdentifier -> Formula a -> Bool
occursFormula x (Forall phi) = occursFormula x phi
occursFormula x (Exists phi) = occursFormula x phi
occursFormula x (Next _ phi) = occursFormula x phi
occursFormula x (RepeatNext _ _ phi) = occursFormula x phi
occursFormula x (Until _ phi psi) = occursFormula x phi || occursFormula x psi
occursFormula x (And phis) = foldl (\acc, phi => acc || occursFormula x phi) False phis
occursFormula x (Or phis) = foldl (\acc, phi => acc || occursFormula x phi) False phis
occursFormula x (Implies phi psi) = occursFormula x phi || occursFormula x psi
occursFormula x (Not phi) = occursFormula x phi
occursFormula _ Bottom = False
occursFormula _ Top = False
occursFormula x (PropForall x' phi) = if x == x' then False else occursFormula x phi
occursFormula x (PropAtom _ is) = foldl (\acc, phi => acc || occursPropConstraint x phi) False (Set.toList is)
occursFormula x (PropEq _ t _) = occursPropTerm x t
