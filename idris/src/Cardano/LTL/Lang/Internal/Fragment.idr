module Cardano.LTL.Lang.Internal.Fragment

import Cardano.LTL.Lang.Formula
import Cardano.LTL.Lang.Internal.Fragment0 as F0
import Cardano.LTL.Lang.Internal.Fragment1 as F1
import Cardano.LTL.Lang.Internal.Fragment2 as F2
import Cardano.LTL.Lang.Internal.GuardedFormula as G
import Data.List
import Data.Maybe
import Data.SortedSet as Set

-- | Try to retract `GuardedFormula` into `Frag0` taking the atom to be the given (x = v).
toFrag0 : Eq ty => Pair PropVarIdentifier PropValue -> G.GuardedFormula ty -> Maybe F0.Frag0
toFrag0 _ (G.Next _ _) = Nothing
toFrag0 abs (G.And phis) = map F0.andList (traverse (toFrag0 abs) phis)
toFrag0 abs (G.Or phis) = map F0.orList (traverse (toFrag0 abs) phis)
toFrag0 abs (G.Implies a b) =
  case (toFrag0 abs a, toFrag0 abs b) of
    (Just a', Just b') => Just (F0.Implies a' b')
    _ => Nothing
toFrag0 abs (G.Not a) = map F0.Not (toFrag0 abs a)
toFrag0 _ G.Top = Just F0.Top
toFrag0 _ G.Bottom = Just F0.Bottom
toFrag0 _ (G.PropForall _ _) = Nothing
toFrag0 (x, v) (G.PropEq rel (Var x') v') =
  if x == x' && v == v' then Just (F0.Atom rel) else Nothing
toFrag0 _ (G.PropEq _ _ _) = Nothing

-- | Evaluate `Frag0` to `Frag1`
toFrag1 : F0.Frag0 -> F1.Frag1
toFrag1 (F0.Atom ty) = F1.Atom ty
toFrag1 (F0.Not x) = F1.notFrag (toFrag1 x)
toFrag1 (F0.And a b) = F1.And (toFrag1 a) (toFrag1 b)
toFrag1 (F0.Or a b) = F1.Or (toFrag1 a) (toFrag1 b)
toFrag1 (F0.Implies a b) = toFrag1 (F0.Or (F0.Not a) b)
toFrag1 F0.Top = F1.Top
toFrag1 F0.Bottom = F1.Bottom

-- | Evaluate `Frag1` to `Frag2`
toFrag2 : F1.Frag1 -> F2.Frag2
toFrag2 (F1.Atom ty) = F2.Atom ty
toFrag2 (F1.NotAtom ty) = F2.NotAtom ty
toFrag2 F1.Bottom = F2.Bottom
toFrag2 F1.Top = F2.Top
toFrag2 (F1.And a b) = F2.andFrag (toFrag2 a) (toFrag2 b)
toFrag2 (F1.Or a b) = F2.orFrag (toFrag2 a) (toFrag2 b)

-- | Embed `Frag2` into `GuardedFormula` interpretting the given pair as (x = v).
export
toGuardedFormula : Pair PropVarIdentifier PropValue -> F2.Frag2 -> G.GuardedFormula ty
toGuardedFormula (x, v) (F2.Atom ty) = G.PropEq ty (Var x) v
toGuardedFormula (x, v) (F2.NotAtom ty) = G.Not (G.PropEq ty (Var x) v)
toGuardedFormula _ F2.Bottom = G.Bottom
toGuardedFormula _ F2.Top = G.Top

export
findAtoms : G.GuardedFormula ty -> Set.SortedSet (Pair PropVarIdentifier PropValue) -> Set.SortedSet (Pair PropVarIdentifier PropValue)
findAtoms (G.Next _ _) set = set
findAtoms (G.And phis) set = foldl (flip findAtoms) set phis
findAtoms (G.Or phis) set = foldl (flip findAtoms) set phis
findAtoms (G.Implies a b) set = findAtoms a (findAtoms b set)
findAtoms (G.Not a) set = findAtoms a set
findAtoms G.Bottom set = set
findAtoms G.Top set = set
findAtoms (G.PropEq _ (Var x) b) set = Set.insert (x, b) set
findAtoms (G.PropEq _ _ _) set = set
findAtoms (G.PropForall _ phi) set = findAtoms phi set

export
normaliseFragment : Eq ty => Set.SortedSet (Pair PropVarIdentifier PropValue) -> G.GuardedFormula ty -> G.GuardedFormula ty
normaliseFragment set phi = go (Set.toList set) where
  go : List (Pair PropVarIdentifier PropValue) -> G.GuardedFormula ty
  go [] = phi
  go (atom :: atoms) =
    case toFrag0 atom phi of
      Just frag0 => toGuardedFormula atom (toFrag2 (toFrag1 frag0))
      Nothing => go atoms
