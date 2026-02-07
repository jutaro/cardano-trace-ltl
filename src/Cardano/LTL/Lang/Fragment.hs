module Cardano.LTL.Lang.Fragment(findAtoms, normaliseFragment) where

import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Lang.Fragment.Fragment0 as F0
import           Cardano.LTL.Lang.Fragment.Fragment1 as F1
import           Cardano.LTL.Lang.Fragment.Fragment2 as F2
import           Cardano.LTL.Lang.GuardedFormula     (GuardedFormula)
import qualified Cardano.LTL.Lang.GuardedFormula     as G
import           Data.Maybe
import           Data.Set                            (Set)
import qualified Data.Set                            as Set
import           Prelude                             hiding (abs, and, not, or)

-- | Try to retract `GuardedFormula` into `Fragment0` taking the atom to be the given (x = v).
retract :: Eq ty => (PropVarIdentifier, PropValue) -> GuardedFormula ty -> Maybe (Fragment0 ty)
retract _ (G.Next {}) = Nothing
retract abs (G.And a b) = F0.And <$> retract abs a <*> retract abs b
retract abs (G.Or a b) = F0.Or <$> retract abs a <*> retract abs b
retract abs (G.Implies a b) = F0.Implies <$> retract abs a <*> retract abs b
retract abs (G.Not a) = F0.Not <$> retract abs a
retract _ G.Top = Just F0.Top
retract _ G.Bottom = Just F0.Bottom
retract _ (G.PropForall {}) = Nothing
retract (!x, !v) (G.PropEq rel (Var x') v') | x == x' && v == v' = Just (F0.Atom rel)
retract _ (G.PropEq {}) = Nothing

-- | Evaluate `Fragment0` to `Fragment1`
toFragment1 :: Fragment0 ty -> Fragment1 ty
toFragment1 (F0.Atom ty)     = F1.Atom ty
toFragment1 (F0.Not x)       = F1.not (toFragment1 x)
toFragment1 (F0.And a b)     = F1.And (toFragment1 a) (toFragment1 b)
toFragment1 (F0.Or a b)      = F1.Or (toFragment1 a) (toFragment1 b)
toFragment1 (F0.Implies a b) = toFragment1 (F0.Not a `F0.Or` b)
toFragment1 F0.Top           = F1.Top
toFragment1 F0.Bottom        = F1.Bottom

-- | Evaluate `Fragment1` to `Fragment2`
toFragment2 :: Ord ty => Fragment1 ty -> Fragment2 ty
toFragment2 (F1.Atom ty)    = F2.Atom ty
toFragment2 (F1.NotAtom ty) = F2.NotAtom ty
toFragment2 F1.Bottom       = F2.Bottom
toFragment2 F1.Top          = F2.Top
toFragment2 (F1.And a b)    = F2.and (toFragment2 a) (toFragment2 b)
toFragment2 (F1.Or a b)     = F2.or (toFragment2 a) (toFragment2 b)

-- | Embed `Fragment2` into `GuardedFormula` interpretting the given pair as (x = v).
toGuardedFormula :: (PropVarIdentifier, PropValue) -> Fragment2 ty -> GuardedFormula ty
toGuardedFormula (!x, !v) (F2.Atom ty)    = G.PropEq ty (Var x) v
toGuardedFormula (!x, !v) (F2.NotAtom ty) = G.Not (G.PropEq ty (Var x) v)
toGuardedFormula _ F2.Bottom              = G.Bottom
toGuardedFormula _ F2.Top                 = G.Top

-- | Find all `Fragment0` atoms in the form of (x = v) in the formula "now".
findAtoms :: GuardedFormula ty -> Set (PropVarIdentifier, PropValue) -> Set (PropVarIdentifier, PropValue)
findAtoms (G.Next _) set             = set
findAtoms (G.And phi psi) set        = findAtoms phi (findAtoms psi set)
findAtoms (G.Or phi psi) set         = findAtoms phi (findAtoms psi set)
findAtoms (G.Implies phi psi) set    = findAtoms phi (findAtoms psi set)
findAtoms (G.Not phi) set            = findAtoms phi set
findAtoms G.Bottom set               = set
findAtoms G.Top set                  = set
findAtoms (G.PropEq _ (Var x) v) set = Set.insert (x, v) set
findAtoms (G.PropEq {}) set          = set
findAtoms (G.PropForall _ phi) set   = findAtoms phi set

-- | Given a set of propositional equalities {xᵢ = vᵢ}ᵢ and a formula, if the formula can be retracted into
--   `Fragment0` where the atom is taken to be one of the equalities (xᵢ = vᵢ), computes normal form in `Fragment0` and
--   embeds the result back into `Formula`. By construction the formula can be retracted for at most one (xᵢ = vᵢ) from the set.
normaliseFragment :: Ord ty => Set (PropVarIdentifier, PropValue) -> GuardedFormula ty -> GuardedFormula ty
normaliseFragment set phi = go (Set.toList set) where
 go [] = phi
 go (atom : atoms) = maybe (go atoms) (toGuardedFormula atom . toFragment2 . toFragment1) (retract atom phi)
