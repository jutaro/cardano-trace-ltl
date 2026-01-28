module Cardano.LTL.Subst (
    substPropTerm
  , substPropConstraint
  , substFormula
  ) where

import           Cardano.LTL.Lang.Formula
import qualified Data.Set                 as Set

-- | t[v / x]
substPropTerm :: PropValue -> PropVarIdentifier -> PropTerm -> PropTerm
substPropTerm v x (Var x') | x == x' = Const v
substPropTerm _ _ t = t

-- | c[v / x]
substPropConstraint :: PropValue -> PropVarIdentifier -> PropConstraint -> PropConstraint
substPropConstraint v x (PropConstraint k t) = PropConstraint k (substPropTerm v x t)

-- | φ[v / x]
substFormula :: PropValue -> PropVarIdentifier -> Formula a -> Formula a
substFormula v x (Forall phi) = Forall (substFormula v x phi)
substFormula v x (ForallN k phi) = ForallN k (substFormula v x phi)
substFormula v x (ExistsN w k phi) = ExistsN w k (substFormula v x phi)
substFormula v x (Next w phi) = Next w (substFormula v x phi)
substFormula v x (NextN w k phi) = NextN w k (substFormula v x phi)
substFormula v x (UntilN w k phi psi) = UntilN w k (substFormula v x phi) (substFormula v x psi)
substFormula v x (And phis) = And $ fmap (substFormula v x) phis
substFormula v x (Or phis) = Or $ fmap (substFormula v x) phis
substFormula v x (Implies phi psi) = Implies (substFormula v x phi) (substFormula v x psi)
substFormula v x (Not phi) = Not (substFormula v x phi)
substFormula _ _ Bottom = Bottom
substFormula _ _ Top = Top
substFormula _ x (PropForall x' e) | x == x' = PropForall x' e
substFormula v x (PropForall x' e) = PropForall x' (substFormula v x e)
substFormula v x (PropAtom c is) = PropAtom c (Set.map (substPropConstraint v x) is)
substFormula v x (PropEq rel t rhs) = PropEq rel (substPropTerm v x t) rhs
