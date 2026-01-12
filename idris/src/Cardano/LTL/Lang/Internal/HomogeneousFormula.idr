module Cardano.LTL.Lang.Internal.HomogeneousFormula

import Cardano.LTL.Lang.Formula
import Cardano.LTL.Lang.Internal.GuardedFormula as G
import Data.SortedSet as Set

public export
data HomogeneousFormula ty =
     Or (List (HomogeneousFormula ty))
   | And (List (HomogeneousFormula ty))
   | Not (HomogeneousFormula ty)
   | Implies (HomogeneousFormula ty) (HomogeneousFormula ty)
   | Top
   | Bottom
   | PropForall PropVarIdentifier (HomogeneousFormula ty)
   | PropEq (Set.SortedSet EventIndex) PropTerm PropValue

export
toGuardedFormula : HomogeneousFormula ty -> G.GuardedFormula ty
toGuardedFormula (And phis) = G.And (map toGuardedFormula phis)
toGuardedFormula (Or phis) = G.Or (map toGuardedFormula phis)
toGuardedFormula (Implies a b) = G.Implies (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Not a) = G.Not (toGuardedFormula a)
toGuardedFormula Bottom = G.Bottom
toGuardedFormula Top = G.Top
toGuardedFormula (PropForall x phi) = G.PropForall x (toGuardedFormula phi)
toGuardedFormula (PropEq e a b) = G.PropEq e a b

export
toFormula : HomogeneousFormula ty -> Formula ty
toFormula (And phis) = And (map toFormula phis)
toFormula (Or phis) = Or (map toFormula phis)
toFormula (Implies a b) = Implies (toFormula a) (toFormula b)
toFormula (Not a) = Not (toFormula a)
toFormula Bottom = Bottom
toFormula Top = Top
toFormula (PropForall x phi) = PropForall x (toFormula phi)
toFormula (PropEq e a b) = PropEq e a b
