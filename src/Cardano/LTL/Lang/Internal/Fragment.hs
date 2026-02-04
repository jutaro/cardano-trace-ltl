module Cardano.LTL.Lang.Internal.Fragment(findAtoms, normaliseFragment) where

import           Cardano.Data.Strict
import           Cardano.LTL.Lang.Formula                 hiding (toFormula)
import           Cardano.LTL.Lang.Internal.Fragment0      as F0
import           Cardano.LTL.Lang.Internal.Fragment1      as F1
import           Cardano.LTL.Lang.Internal.Fragment2      as F2
import           Cardano.LTL.Lang.Internal.GuardedFormula (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula as G
import           Data.Maybe
import           Data.Set                                 (Set)
import qualified Data.Set                                 as Set
import           Prelude                                  hiding (and, not, or)

-- | Try to retract `GuardedFormula` into `Frag0` taking the atom to be the given (x = v).
toFrag0 :: Eq ty => Pair PropVarIdentifier PropValue -> GuardedFormula ty -> Maybe Frag0
toFrag0 _ (G.Next {}) = Nothing
toFrag0 abs (G.And a b) = F0.And <$> toFrag0 abs a <*> toFrag0 abs b
toFrag0 abs (G.Or a b) = F0.Or <$> toFrag0 abs a <*> toFrag0 abs b
toFrag0 abs (G.Implies a b) = F0.Implies <$> toFrag0 abs a <*> toFrag0 abs b
toFrag0 abs (G.Not a) = F0.Not <$> toFrag0 abs a
toFrag0 _ G.Top = Just F0.Top
toFrag0 _ G.Bottom = Just F0.Bottom
toFrag0 _ (G.PropForall {}) = Nothing
toFrag0 (Pair x v) f@(G.PropEq rel (Var x') v') | x == x' && v == v' = Just (F0.Atom rel)
toFrag0 _ f@(G.PropEq {}) = Nothing

-- | Evaluate `Frag0` to `Frag1`
toFrag1 :: Frag0 -> Frag1
toFrag1 (F0.Atom ty)     = F1.Atom ty
toFrag1 (F0.Not x)       = F1.not (toFrag1 x)
toFrag1 (F0.And a b)     = F1.And (toFrag1 a) (toFrag1 b)
toFrag1 (F0.Or a b)      = F1.Or (toFrag1 a) (toFrag1 b)
toFrag1 (F0.Implies a b) = toFrag1 (F0.Not a `F0.Or` b)
toFrag1 F0.Top           = F1.Top
toFrag1 F0.Bottom        = F1.Bottom

-- | Evaluate `Frag1` to `Frag2`
toFrag2 :: Frag1 -> Frag2
toFrag2 (F1.Atom ty)    = F2.Atom ty
toFrag2 (F1.NotAtom ty) = F2.NotAtom ty
toFrag2 F1.Bottom       = F2.Bottom
toFrag2 F1.Top          = F2.Top
toFrag2 (F1.And a b)    = F2.and (toFrag2 a) (toFrag2 b)
toFrag2 (F1.Or a b)     = F2.or (toFrag2 a) (toFrag2 b)

-- | Embed `Frag2` into `GuardedFormula` interpretting the given pair as (x = v).
toGuardedFormula :: Pair PropVarIdentifier PropValue -> Frag2 -> GuardedFormula ty
toGuardedFormula (Pair x v) (F2.Atom ty)    = G.PropEq ty (Var x) v
toGuardedFormula (Pair x v) (F2.NotAtom ty) = G.Not (G.PropEq ty (Var x) v)
toGuardedFormula _ F2.Bottom                = G.Bottom
toGuardedFormula _ F2.Top                   = G.Top

-- | Find all `Frag0` atoms in the form of (x = v) in the formula "now".
findAtoms :: GuardedFormula ty -> Set (Pair PropVarIdentifier PropValue) -> Set (Pair PropVarIdentifier PropValue)
findAtoms (G.Next w phi) set       = set
findAtoms (G.And a b) set          = findAtoms a (findAtoms b set)
findAtoms (G.Or a b) set           = findAtoms a (findAtoms b set)
findAtoms (G.Implies a b) set      = findAtoms a (findAtoms b set)
findAtoms (G.Not a) set            = findAtoms a set
findAtoms G.Bottom set             = set
findAtoms G.Top set                = set
findAtoms (G.PropEq _ (Var x) b) set = Set.insert (Pair x b) set
findAtoms (G.PropEq _ a b) set       = set
findAtoms (G.PropForall _ phi) set = findAtoms phi set

-- | Given a set of propositional equalities {xᵢ = vᵢ}ᵢ and a formula, if the formula can be retracted into
--   `Frag0` where the atom is taken to be one of the equalities (xᵢ = vᵢ), computes normal form in `Frag0` and
--   embeds the result back into `Formula`. By construction the formula can be retracted for at most one (xᵢ = vᵢ) from the set.
normaliseFragment :: Eq ty => Set (Pair PropVarIdentifier PropValue) -> GuardedFormula ty -> GuardedFormula ty
normaliseFragment set phi = go (Set.toList set) where
 go [] = phi
 go (atom : atoms) = maybe (go atoms) (toGuardedFormula atom . toFrag2 . toFrag1) (toFrag0 atom phi)
