module Cardano.LTL.Occurs (
    occursPropTerm
  , occursPropConstraint
  , occursFormula
  ) where

import           Cardano.LTL.Lang.Formula
import qualified Data.Set                 as Set
import           Data.Text                (Text)

occursPropTerm :: Text -> PropTerm -> Bool
occursPropTerm _ (Const _) = False
occursPropTerm x (Var x')  = x == x'

occursPropConstraint :: Text -> PropConstraint -> Bool
occursPropConstraint x (PropConstraint _ t) = occursPropTerm x t

occursFormula :: Text -> Formula a -> Bool
occursFormula x (Forall phi) = occursFormula x phi
occursFormula x (Exists phi) = occursFormula x phi
occursFormula x (Next w phi) = occursFormula x phi
occursFormula x (RepeatNext w k phi) = occursFormula x phi
occursFormula x (Until w phi psi) = occursFormula x phi || occursFormula x psi
occursFormula x (And phis) = foldl' (\acc phi -> acc || occursFormula x phi) False phis
occursFormula x (Or phis) = foldl' (\acc phi -> acc || occursFormula x phi) False phis
occursFormula x (Implies phi psi) = occursFormula x phi || occursFormula x psi
occursFormula x (Not phi) = occursFormula x phi
occursFormula _ Bottom = False
occursFormula _ Top = False
occursFormula x (PropForall x' _) | x == x' = False
occursFormula x (PropForall _ phi) = occursFormula x phi
occursFormula x (PropAtom c is) = foldl' (\acc phi -> acc || occursPropConstraint x phi) False is
occursFormula x (PropEq t _) = occursPropTerm x t
