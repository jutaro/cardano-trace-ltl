{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang.Internal.HomogeneousFormula (
    HomogeneousFormula(..)
  , toGuardedFormula, toFormula, values, substHomogeneousFormula, interp, equiv) where

import           Cardano.LTL.Lang.Formula                 (EventIndex, Formula,
                                                           PropTerm, PropValue,
                                                           PropVarIdentifier)
import qualified Cardano.LTL.Lang.Formula                 as F
import           Cardano.LTL.Lang.Internal.GuardedFormula (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula as G
import           Cardano.LTL.Subst                        (substPropTerm)
import           Data.Function                            (on)
import           Data.Functor                             ((<&>))
import qualified Data.Map                                 as Map
import           Data.Map.Strict                          (Map)
import           Data.Set                                 (Set, union)
import qualified Data.Set                                 as Set
import           Data.Text                                (Text)

data ExtendedPropValue = Val PropValue | Placeholder deriving (Show, Ord, Eq)

-- | A `Formula` with no temporal operators.
--   Equivalence of two `HomogeneousFormula`s is decidable.
data HomogeneousFormula =
   ------------ Connective -------------
     Or HomogeneousFormula HomogeneousFormula
   | And HomogeneousFormula HomogeneousFormula
   | Not HomogeneousFormula
   | Implies HomogeneousFormula HomogeneousFormula
   | Top
   | Bottom
   -------------------------------------


   ----------- Event property ----------
   | PropForall PropVarIdentifier HomogeneousFormula
   | PropEq (Set EventIndex) PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------

toGuardedFormula :: HomogeneousFormula -> GuardedFormula ty
toGuardedFormula (And a b)             = G.And (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Or a b)              = G.Or (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Implies a b)         = G.Implies (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Not a)               = G.Not (toGuardedFormula a)
toGuardedFormula Bottom                = G.Bottom
toGuardedFormula Top                   = G.Top
toGuardedFormula (PropEq e a b)        = G.PropEq e a b
toGuardedFormula (PropForall x phi)    = G.PropForall x (toGuardedFormula phi)

toFormula :: HomogeneousFormula -> Formula ty
toFormula (And a b)          = F.And (toFormula a) (toFormula b)
toFormula (Or a b)           = F.Or (toFormula a) (toFormula b)
toFormula (Implies a b)      = F.Implies (toFormula a) (toFormula b)
toFormula (Not a)            = F.Not (toFormula a)
toFormula Bottom             = F.Bottom
toFormula Top                = F.Top
toFormula (PropEq e a b)     = F.PropEq e a b
toFormula (PropForall x phi) = F.PropForall x (toFormula phi)

valuesAccum :: Set PropValue -> PropVarIdentifier -> HomogeneousFormula -> Set PropValue
valuesAccum acc x (Or phi psi) = valuesAccum (valuesAccum acc x phi) x psi
valuesAccum acc x (And phi psi) = valuesAccum (valuesAccum acc x phi) x psi
valuesAccum acc x (Not phi) = valuesAccum acc x phi
valuesAccum acc x (Implies phi psi) = valuesAccum (valuesAccum acc x phi) x psi
valuesAccum acc x Top = acc
valuesAccum acc x Bottom = acc
valuesAccum acc x (PropEq rel (F.Const _) v) = acc
valuesAccum acc x (PropEq rel (F.Var x') v) | x == x' = Set.insert v acc
valuesAccum acc x (PropEq rel (F.Var x') v) = acc
valuesAccum acc x (PropForall x' phi) | x /= x' = valuesAccum acc x phi
valuesAccum acc x (PropForall x' phi) = acc

-- | Set of values the given prop var can take in the formula.
values :: PropVarIdentifier -> HomogeneousFormula -> Set PropValue
values = valuesAccum Set.empty

-- | φ[v / x]
substHomogeneousFormula :: ExtendedPropValue -> PropVarIdentifier -> HomogeneousFormula -> HomogeneousFormula
substHomogeneousFormula v x (And phi psi) = And (substHomogeneousFormula v x phi) (substHomogeneousFormula v x psi)
substHomogeneousFormula v x (Or phi psi) = Or (substHomogeneousFormula v x phi) (substHomogeneousFormula v x psi)
substHomogeneousFormula v x (Implies phi psi) = Implies (substHomogeneousFormula v x phi) (substHomogeneousFormula v x psi)
substHomogeneousFormula v x (Not phi) = Not (substHomogeneousFormula v x phi)
substHomogeneousFormula _ _ Bottom = Bottom
substHomogeneousFormula _ _ Top = Top
substHomogeneousFormula v x (PropEq rel (F.Const v') rhs) = PropEq rel (F.Const v') rhs
-- (x = v)[☐ / x] = ⊥
-- i.e. the placeholder value is distinct from all possible `PropValue`s
substHomogeneousFormula Placeholder x (PropEq rel (F.Var x') rhs) | x == x' = Bottom
substHomogeneousFormula (Val v) x (PropEq rel (F.Var x') rhs) | x == x' = PropEq rel (F.Const v) rhs
substHomogeneousFormula _ x (PropEq rel (F.Var x') rhs) = PropEq rel (F.Var x') rhs
substHomogeneousFormula v x (PropForall x' phi) | x /= x' = PropForall x' (substHomogeneousFormula v x phi)
substHomogeneousFormula v x (PropForall x' phi) = PropForall x' phi

-- | Interpret the `HomogeneousFormula` onto `Bool`
interp :: HomogeneousFormula -> Bool
interp (Or phi psi) = interp phi || interp psi
interp (And phi psi) = interp phi && interp psi
interp (Not phi) = not (interp phi)
interp (Implies phi psi) = not (interp phi) || interp psi
interp Bottom = False
interp Top = True
interp (PropEq rel (F.Const lhs) rhs) = lhs == rhs
interp (PropEq rel (F.Var x) rhs) = error $ "interp: free variable " <> show x
-- ⟦∀x. φ⟧ <=> φ[☐/x] ∧ φ[v₁ / x] ∧ ... ∧ φ[vₖ / x] where v₁...vₖ is the set of values in φ which x can take.
interp (PropForall x phi) = interp (substHomogeneousFormula Placeholder x phi) &&
  foldl' (&&) True (
    Set.toList (values x phi) <&> \v ->
      interp (substHomogeneousFormula (Val v) x phi)
  )

-- | Check equivalence of two `HomogeneousFormula`s.
equiv :: HomogeneousFormula -> HomogeneousFormula -> Bool
equiv = on (==) interp
