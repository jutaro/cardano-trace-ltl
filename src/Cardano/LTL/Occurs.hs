module Cardano.LTL.Occurs (
    occursPropTerm
  , occursPropConstraint
  , occursFormula
  ) where

import           Cardano.LTL.Lang.Formula
import qualified Data.Set                 as Set

-- | Check if the `PropVarIdentifier` occurs freely in the `PropTerm`.
occursPropTerm :: PropVarIdentifier -> PropTerm -> Bool
occursPropTerm _ (Const _) = False
occursPropTerm x (Var x')  = x == x'

-- | Check if the `PropVarIdentifier` occurs freely in the `PropConstraint`.
occursPropConstraint :: PropVarIdentifier -> PropConstraint -> Bool
occursPropConstraint x (PropConstraint _ t) = occursPropTerm x t

-- | Check if the `PropVarIdentifier` occurs freely in the `Formula`.
occursFormula :: PropVarIdentifier -> Formula a -> Bool
occursFormula x (Forall phi) = occursFormula x phi
occursFormula x (ForallN _ phi) = occursFormula x phi
occursFormula x (ExistsN _ _ phi) = occursFormula x phi
occursFormula x (Next _ phi) = occursFormula x phi
occursFormula x (NextN _ k phi) = occursFormula x phi
occursFormula x (UntilN _ _ phi psi) = occursFormula x phi || occursFormula x psi
occursFormula x (And phis) = foldl' (\acc phi -> acc || occursFormula x phi) False phis
occursFormula x (Or phis) = foldl' (\acc phi -> acc || occursFormula x phi) False phis
occursFormula x (Implies phi psi) = occursFormula x phi || occursFormula x psi
occursFormula x (Not phi) = occursFormula x phi
occursFormula _ Bottom = False
occursFormula _ Top = False
occursFormula x (PropForall x' _) | x == x' = False
occursFormula x (PropForall _ phi) = occursFormula x phi
occursFormula x (PropAtom _ is) = foldl' (\acc phi -> acc || occursPropConstraint x phi) False is
occursFormula x (PropEq _ t _) = occursPropTerm x t
