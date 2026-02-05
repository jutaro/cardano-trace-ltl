{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang.Internal.HomogeneousFormula (
    HomogeneousFormula(..)
  , toGuardedFormula, toFormula, values, substHomogeneousFormula, interp, quote, equiv) where

import           Cardano.LTL.Lang.Formula                 (Formula, PropTerm,
                                                           PropValue,
                                                           PropVarIdentifier,
                                                           Relevance)
import qualified Cardano.LTL.Lang.Formula                 as F
import           Cardano.LTL.Lang.Internal.GuardedFormula (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula as G
import           Data.Function                            (on)
import           Data.Functor                             ((<&>))
import           Data.Set                                 (Set)
import qualified Data.Set                                 as Set

data ExtendedPropValue = Val PropValue | Placeholder deriving (Show, Ord, Eq)

-- | A `Formula` with no temporal operators.
--   Equivalence of two `HomogeneousFormula`s is decidable.
data HomogeneousFormula ty =
   ------------ Connective -------------
     Or (HomogeneousFormula ty) (HomogeneousFormula ty)
   | And (HomogeneousFormula ty) (HomogeneousFormula ty)
   | Not (HomogeneousFormula ty)
   | Implies (HomogeneousFormula ty) (HomogeneousFormula ty)
   | Top
   | Bottom
   -------------------------------------


   ----------- Event property ----------
   | PropForall PropVarIdentifier (HomogeneousFormula ty)
   | PropEq (Relevance ty) PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------

toGuardedFormula :: HomogeneousFormula ty -> GuardedFormula ty
toGuardedFormula (And a b)             = G.And (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Or a b)              = G.Or (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Implies a b)         = G.Implies (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Not a)               = G.Not (toGuardedFormula a)
toGuardedFormula Bottom                = G.Bottom
toGuardedFormula Top                   = G.Top
toGuardedFormula (PropEq e a b)        = G.PropEq e a b
toGuardedFormula (PropForall x phi)    = G.PropForall x (toGuardedFormula phi)

toFormula :: HomogeneousFormula ty -> Formula ty
toFormula (And a b)          = F.And (toFormula a) (toFormula b)
toFormula (Or a b)           = F.Or (toFormula a) (toFormula b)
toFormula (Implies a b)      = F.Implies (toFormula a) (toFormula b)
toFormula (Not a)            = F.Not (toFormula a)
toFormula Bottom             = F.Bottom
toFormula Top                = F.Top
toFormula (PropEq e a b)     = F.PropEq e a b
toFormula (PropForall x phi) = F.PropForall x (toFormula phi)

valuesAccum :: Set PropValue -> PropVarIdentifier -> HomogeneousFormula ty -> Set PropValue
valuesAccum acc x (Or phi psi) = valuesAccum (valuesAccum acc x phi) x psi
valuesAccum acc x (And phi psi) = valuesAccum (valuesAccum acc x phi) x psi
valuesAccum acc x (Not phi) = valuesAccum acc x phi
valuesAccum acc x (Implies phi psi) = valuesAccum (valuesAccum acc x phi) x psi
valuesAccum acc _ Top = acc
valuesAccum acc _ Bottom = acc
valuesAccum acc _ (PropEq _ (F.Const _) _) = acc
valuesAccum acc x (PropEq _ (F.Var x') v) | x == x' = Set.insert v acc
valuesAccum acc _ (PropEq _ (F.Var _) _) = acc
valuesAccum acc x (PropForall x' phi) | x /= x' = valuesAccum acc x phi
valuesAccum acc _ (PropForall _ _i) = acc

-- | Set of values the given prop var can take in the formula.
values :: PropVarIdentifier -> HomogeneousFormula ty -> Set PropValue
values = valuesAccum Set.empty

-- | φ[v / x]
substHomogeneousFormula :: ExtendedPropValue -> PropVarIdentifier -> HomogeneousFormula ty -> HomogeneousFormula ty
substHomogeneousFormula v x (And phi psi) = And (substHomogeneousFormula v x phi) (substHomogeneousFormula v x psi)
substHomogeneousFormula v x (Or phi psi) = Or (substHomogeneousFormula v x phi) (substHomogeneousFormula v x psi)
substHomogeneousFormula v x (Implies phi psi) = Implies (substHomogeneousFormula v x phi) (substHomogeneousFormula v x psi)
substHomogeneousFormula v x (Not phi) = Not (substHomogeneousFormula v x phi)
substHomogeneousFormula _ _ Bottom = Bottom
substHomogeneousFormula _ _ Top = Top
substHomogeneousFormula _ _ (PropEq rel (F.Const v') rhs) = PropEq rel (F.Const v') rhs
-- (x = v)[☐ / x] = ⊥
-- i.e. the placeholder value is distinct from all possible `PropValue`s
substHomogeneousFormula Placeholder x (PropEq _ (F.Var x') _) | x == x' = Bottom
substHomogeneousFormula (Val v) x (PropEq rel (F.Var x') rhs) | x == x' = PropEq rel (F.Const v) rhs
substHomogeneousFormula _ _ (PropEq rel (F.Var x') rhs) = PropEq rel (F.Var x') rhs
substHomogeneousFormula v x (PropForall x' phi) | x /= x' = PropForall x' (substHomogeneousFormula v x phi)
substHomogeneousFormula _ _ (PropForall x' phi) = PropForall x' phi

-- | Interpret the `HomogeneousFormula` onto `Bool`.
--   This is the "interesting" part of the iso: `HomogeneousFormula` ≅ `Bool`
interp :: HomogeneousFormula ty -> Bool
interp (Or phi psi) = interp phi || interp psi
interp (And phi psi) = interp phi && interp psi
interp (Not phi) = not (interp phi)
interp (Implies phi psi) = not (interp phi) || interp psi
interp Bottom = False
interp Top = True
interp (PropEq _ (F.Const lhs) rhs) = lhs == rhs
interp (PropEq _ (F.Var x) _) = error $ "interp: free variable " <> show x
-- ⟦∀x. φ⟧ <=> φ[☐/x] ∧ φ[v₁ / x] ∧ ... ∧ φ[vₖ / x] where v₁...vₖ is the set of values in φ which x can take.
interp (PropForall x phi) = interp (substHomogeneousFormula Placeholder x phi) &&
  foldl' (&&) True (
    Set.toList (values x phi) <&> \v ->
      interp (substHomogeneousFormula (Val v) x phi)
  )

-- | This is the "easy" part of the iso: `HomogeneousFormula` ≅ `Bool`
quote :: Bool -> HomogeneousFormula ty
quote True = Top
quote False = Bottom

-- | Check equivalence of two `HomogeneousFormula`s.
equiv :: HomogeneousFormula ty -> HomogeneousFormula ty -> Bool
equiv = on (==) interp
