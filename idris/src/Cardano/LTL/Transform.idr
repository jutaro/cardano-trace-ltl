module Cardano.LTL.Transform

import Cardano.LTL.Lang.Formula
import Cardano.LTL.Lang.Internal.Fragment 
import Cardano.LTL.Lang.Internal.GuardedFormula as G
import Cardano.LTL.Lang.Internal.HomogeneousFormula as H
import Cardano.LTL.Occurs 
import Cardano.LTL.Subst 
import Data.List
import Data.SortedMap as Map
import Data.SortedSet as Set

export
step : (Event event ty, Eq ty) => Formula ty -> event -> G.GuardedFormula ty
step (Forall phi) s = G.And [step phi s, G.Next True (Forall phi)]
step (Exists phi) s = G.Or [step phi s, G.Next False (Exists phi)]
step (Next w phi) _ = G.Next w phi
step (RepeatNext _ 0 phi) s = step phi s
step (RepeatNext w k phi) s = G.Or [step phi s, G.Next w (RepeatNext w (k - 1) phi)]
step (Until w phi psi) s = G.Or [step psi s, G.And [G.Not (step psi s), step phi s, G.Next w (Until w phi psi)]]
step (And phis) s = G.And (map (\x => step x s) phis)
step (Or phis) s = G.Or (map (\x => step x s) phis)
step (Implies phi psi) s = G.Implies (step phi s) (step psi s)
step (Not phi) s = G.Not (step phi s)
step Bottom _ = G.Bottom
step Top _ = G.Top
step (PropAtom c is) s =
  if ofTy s c then
    let evalConstraint : {auto _ : Event event ty} -> PropConstraint -> G.GuardedFormula ty
        evalConstraint (MkPropConstraint key t) = ?p1
          -- case Map.lookup key (props s c) of
          --   Just v => G.PropEq (Set.insert (index s) Set.empty) t v
          --   Nothing => G.Bottom
    in G.And (map evalConstraint (Set.toList is))
  else
    G.Bottom
step (PropForall x phi) s = G.PropForall x (step phi s)
step (PropEq rel a b) _ = G.PropEq rel a b

export
terminate : Formula a -> H.HomogeneousFormula a
terminate (Forall _) = H.Top
terminate (Exists _) = H.Bottom
terminate (RepeatNext True _ _) = H.Top
terminate (RepeatNext False 0 phi) = terminate phi
terminate (RepeatNext False _ _) = H.Bottom
terminate (Until True _ _) = H.Top
terminate (Until False _ _) = H.Bottom
terminate (PropAtom _ _) = H.Bottom
terminate (Next True _) = H.Top
terminate (Next False _) = H.Bottom
terminate (And phis) = H.And (map terminate phis)
terminate (Or phis) = H.Or (map terminate phis)
terminate (Implies phi psi) = H.Implies (terminate phi) (terminate psi)
terminate (Not phi) = H.Not (terminate phi)
terminate Bottom = H.Bottom
terminate Top = H.Top
terminate (PropForall x phi) = H.PropForall x (terminate phi)
terminate (PropEq rel a b) = H.PropEq rel a b

end : Formula a -> Bool
end (Forall _) = True
end (Exists _) = False
end (Next w _) = w
end (RepeatNext _ 0 phi) = end phi
end (RepeatNext w _ _) = w
end (Until w _ _) = w
end (And phis) = all id (map end phis)
end (Or phis) = any id (map end phis)
end (Implies phi psi) = not (end phi) || end psi
end (Not phi) = not (end phi)
end Bottom = False
end Top = True
end (PropAtom _ _) = False
end (PropForall x phi) = not (occursFormula x phi) && end phi
end (PropEq _ (Const v) v') = v == v'
end (PropEq _ (Var _) _) = False

export
simplifyNext : G.GuardedFormula ty -> G.GuardedFormula ty
simplifyNext (G.Next w phi) = pushNext w phi where
  pushNext : Bool -> Formula ty -> G.GuardedFormula ty
  pushNext w (Forall phi) = G.Next w (Forall phi)
  pushNext w (Exists phi) = G.Next w (Exists phi)
  pushNext w (Next w' phi) = G.Next w (Next w' phi)
  pushNext w (RepeatNext w' k phi) = G.Next w (RepeatNext w' k phi)
  pushNext w (Until w' phi psi) = G.Next w (Until w' phi psi)
  pushNext w (And phis) = G.And (map (pushNext w) phis)
  pushNext w (Or phis) = G.Or (map (pushNext w) phis)
  pushNext w (Implies a b) = G.Implies (pushNext w a) (pushNext w b)
  pushNext w (Not a) = G.Not (pushNext w a)
  pushNext _ Bottom = G.Bottom
  pushNext _ Top = G.Top
  pushNext _ (PropEq rel a b) = G.PropEq rel a b
  pushNext w (PropAtom c a) = G.Next w (PropAtom c a)
  pushNext w (PropForall x phi) = G.PropForall x (pushNext w phi)
simplifyNext (G.And phis) = G.And (map simplifyNext phis)
simplifyNext (G.Or phis) = G.Or (map simplifyNext phis)
simplifyNext (G.Implies a b) = G.Implies (simplifyNext a) (simplifyNext b)
simplifyNext (G.Not phi) = G.Not (simplifyNext phi)
simplifyNext G.Bottom = G.Bottom
simplifyNext G.Top = G.Top
simplifyNext (G.PropEq rel a b) = G.PropEq rel a b
simplifyNext (G.PropForall x phi) = G.PropForall x (simplifyNext phi)

export
simplifyFragment : Eq ty => G.GuardedFormula ty -> G.GuardedFormula ty
simplifyFragment {ty} phi = go (findAtoms phi Set.empty) phi where
  go : {0 ty' : Type} -> Eq ty' => Set.SortedSet (Pair PropVarIdentifier PropValue) -> G.GuardedFormula ty' -> G.GuardedFormula ty'
  go _ (G.Next w phi) = G.Next w phi
  go atoms (G.And phis) =
    let phis' = map (go atoms) phis in
    normaliseFragment atoms (G.And phis')
  go atoms (G.Or phis) =
    let phis' = map (go atoms) phis in
    normaliseFragment atoms (G.Or phis')
  go atoms (G.Implies a b) =
    let a' = go atoms a
        b' = go atoms b
    in normaliseFragment atoms (G.Implies a' b')
  go atoms (G.Not phi) =
    let phi' = go atoms phi in
    normaliseFragment atoms (G.Not phi')
  go _ G.Bottom = G.Bottom
  go _ G.Top = G.Top
  go _ (G.PropEq rel a b) = G.PropEq rel a b
  go atoms (G.PropForall x phi) = G.PropForall x (go atoms phi)

export
simplify : Eq (Formula ty) => Eq ty => Formula ty -> Formula ty
simplify (Forall phi) =
  case simplify phi of
    Top => Top
    Bottom => Bottom
    phi' => Forall phi'
simplify (Exists phi) =
  case simplify phi of
    Top => Top
    Bottom => Bottom
    phi' => Exists phi'
simplify (Next w phi) = Next w (simplify phi)
simplify (RepeatNext w 0 phi) = simplify phi
simplify (RepeatNext w k phi) = RepeatNext w k (simplify phi)
simplify (Until w phi psi) =
  case simplify psi of
    Top => Top
    Bottom => simplify phi
    psi' => Until w (simplify phi) psi'
simplify (And phis) =
  let phis' = filter (/= Top) (map simplify phis) in
  case find (== Bottom) phis' of
    Nothing =>
      case phis' of
        [] => Top
        [phi] => phi
        _ => And phis'
    Just _ => Bottom
simplify (Or phis) =
  let phis' = filter (/= Bottom) (map simplify phis) in
  case find (== Top) phis' of
    Nothing =>
      case phis' of
        [] => Bottom
        [phi] => phi
        _ => Or phis'
    Just _ => Top
simplify (Implies a b) =
  case (simplify a, simplify b) of
    (Top, b') => b'
    (Bottom, _) => Top
    (_, Top) => Top
    (a', Bottom) => simplify (Not a')
    (a', b') => Implies a' b'
simplify (Not a) =
  case simplify a of
    Not a' => a'
    Top => Bottom
    Bottom => Top
    a' => Not a'
simplify Bottom = Bottom
simplify Top = Top
simplify (PropEq _ (Const v) v') = if v == v' then Top else Bottom
simplify p@(PropEq _ _ _) = p
simplify p@(PropAtom _ _) = p
simplify (PropForall x phi) =
  case simplify phi of
    Top => Top
    Bottom => Bottom
    phi' => PropForall x phi'
