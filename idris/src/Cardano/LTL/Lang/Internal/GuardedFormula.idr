module Cardano.LTL.Lang.Internal.GuardedFormula

import Cardano.LTL.Lang.Formula
import Data.SortedSet as Set

public export
data GuardedFormula ty =
     Next Bool (Formula ty)
   | Or (List (GuardedFormula ty))
   | And (List (GuardedFormula ty))
   | Not (GuardedFormula ty)
   | Implies (GuardedFormula ty) (GuardedFormula ty)
   | Top
   | Bottom
   | PropForall PropVarIdentifier (GuardedFormula ty)
   | PropEq (Set.SortedSet EventIndex) PropTerm PropValue

export
toFormula : GuardedFormula ty -> Formula ty
toFormula (Next w phi) = Next w phi
toFormula (And phis) = And (map toFormula phis)
toFormula (Or phis) = Or (map toFormula phis)
toFormula (Implies a b) = Implies (toFormula a) (toFormula b)
toFormula (Not a) = Not (toFormula a)
toFormula Bottom = Bottom
toFormula Top = Top
toFormula (PropForall x phi) = PropForall x (toFormula phi)
toFormula (PropEq e a b) = PropEq e a b

export
forward : GuardedFormula ty -> Formula ty
forward (Next _ phi) = phi
forward (And phis) = And (map forward phis)
forward (Or phis) = Or (map forward phis)
forward (Implies phi psi) = Implies (forward phi) (forward psi)
forward (Not phi) = Not (forward phi)
forward Bottom = Bottom
forward Top = Top
forward (PropForall x phi) = PropForall x (forward phi)
forward (PropEq e a b) = PropEq e a b
