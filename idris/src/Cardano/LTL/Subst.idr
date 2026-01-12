module Cardano.LTL.Subst

import Cardano.LTL.Lang.Formula
import Data.SortedSet as Set

substPropTerm : PropValue -> PropVarIdentifier -> PropTerm -> PropTerm
substPropTerm v x (Var x') = if x == x' then Const v else Var x'
substPropTerm _ _ t = t

substPropConstraint : PropValue -> PropVarIdentifier -> PropConstraint -> PropConstraint
substPropConstraint v x (MkPropConstraint k t) = MkPropConstraint k (substPropTerm v x t)

export
substFormula : PropValue -> PropVarIdentifier -> Formula a -> Formula a
substFormula v x (Forall phi) = Forall (substFormula v x phi)
substFormula v x (Exists phi) = Exists (substFormula v x phi)
substFormula v x (Next w phi) = Next w (substFormula v x phi)
substFormula v x (RepeatNext w k phi) = RepeatNext w k (substFormula v x phi)
substFormula v x (Until w phi psi) = Until w (substFormula v x phi) (substFormula v x psi)
substFormula v x (And phis) = And (map (substFormula v x) phis)
substFormula v x (Or phis) = Or (map (substFormula v x) phis)
substFormula v x (Implies phi psi) = Implies (substFormula v x phi) (substFormula v x psi)
substFormula v x (Not phi) = Not (substFormula v x phi)
substFormula _ _ Bottom = Bottom
substFormula _ _ Top = Top
substFormula v x (PropForall x' e) = if x == x' then PropForall x' e else PropForall x' (substFormula v x e)
substFormula v x (PropAtom c is) = PropAtom c (Set.fromList (map (substPropConstraint v x) (Prelude.toList is)))
substFormula v x (PropEq rel t rhs) = PropEq rel (substPropTerm v x t) rhs
