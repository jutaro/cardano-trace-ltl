{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Transform(
    step
  , end
  , Relevance(..)
  , simplify
  ) where

import           Cardano.LTL.Lang
import           Cardano.LTL.Subst (substFormula)
import           Data.List         hiding (lookup)
import           Data.Map.Strict   (lookup)
import qualified Data.Set          as Set
import           Data.Text         (unpack)
import           Prelude           hiding (lookup)

-- | Applicative-functor of relevance tracking. Product is relevant if either of the constituents is.
data Relevance a = Relevant Bool a

instance Functor Relevance where
  fmap f (Relevant t x) = Relevant t (f x)

instance Applicative Relevance where
  pure = Relevant False
  Relevant b f <*> Relevant b' x = Relevant (b || b') (f x)

-- | Tag a computation as irrelevant to the current step.
irrelevant :: a -> Relevance a
irrelevant = Relevant False

-- | Tag a computation as relevant to the current step.
relevant :: a -> Relevance a
relevant = Relevant True

-- | Fast forwards the formula through the given event.
-- | Returns an equivalent formula and whether the event is "relevant".
-- | An event is relevant in a formula iff the formula contains an atom of that event type "now".
step :: (Event m ty, Eq ty) => Formula ty -> m -> Relevance (Formula ty)
step (Forall phi) s = (\x -> And [x, Forall phi]) <$> step phi s
step (Exists phi) s = (\x -> Or [x, Exists phi]) <$> step phi s
step (Next _ phi) _ = irrelevant phi
step (RepeatNext _ 0 phi) s = step phi s
step (RepeatNext w k phi) s = (\x -> Or [x, RepeatNext w (k - 1) phi]) <$> step phi s
step (Until w phi psi) s = (\x y -> Or [x, And [y, Until w phi psi]]) <$> step psi s <*> step phi s
step (And phis) s = And <$> traverse (`step` s) phis
step (Or phis) s = Or <$> traverse (`step` s) phis
step (Implies phi psi) s = Implies <$> step phi s <*> step psi s
step (Not phi) s = Not <$> step phi s
step Bottom _ = irrelevant Bottom
step Top _ = irrelevant Top
step (PropAtom c is) s | ty s == c =
  relevant $ And $ flip fmap (Set.toList is) $ \(PropConstraint key t) ->
    case lookup key (props s) of
      Just v  -> PropEq t v
      -- NOTE: Shall we have a config option for either crashing hard or returning ⊥ in case there is no such key?
      Nothing -> Bottom
step (PropForall x phi) s = PropForall x <$> step phi s
step (PropAtom _ _) _ = irrelevant Bottom
step (PropEq a b) _ = irrelevant $ PropEq a b

-- | Check if the formula is a tautology, assuming the end of timeline.
end :: [PropValue] -> Formula a -> Bool
end _ (Forall _)              = True
end _ (Exists _)              = False
end _ (Next w _)              = w
end idxs (RepeatNext _ 0 phi) = end idxs phi
end _ (RepeatNext w _ _)      = w
end _ (Until w _ _)           = w
end idxs (And phis)           = foldl' (&&) True (fmap (end idxs) phis)
end idxs (Or phis)            = foldl' (||) False (fmap (end idxs) phis)
end idxs (Implies phi psi)    = not (end idxs phi) || end idxs psi
end idxs (Not phi)            = not (end idxs phi)
end _ Bottom                  = False
end _ Top                     = True
end _ (PropAtom _ _)          = False
end idxs (PropForall x phi)   = foldl' (\acc idx -> acc && end idxs (substFormula idx x phi)) True idxs
end _ (PropEq (Const v) v')   = v == v'
end _ (PropEq (Var x) _)      = error $ "Encountered a var: " <> unpack x

simplify :: Eq ty => Formula ty -> Formula ty
simplify (Forall phi) =
  case simplify phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> Forall phi
simplify (Exists phi) =
  case simplify phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> Exists phi
simplify (Next w phi) = Next w (simplify phi)
simplify (RepeatNext w 0 phi) = simplify phi
simplify (RepeatNext w k phi) = RepeatNext w k (simplify phi)
simplify (Until w phi psi) =
  case simplify psi of
    Top    -> Top
    Bottom -> simplify phi
    psi    -> Until w (simplify phi) psi
simplify (And phis) =
  let phis' = filter (/= Top) (fmap simplify phis) in
  case find (== Bottom) phis' of
    Nothing ->
      case phis' of
        []    -> Top
        [phi] -> phi
        phis' -> And phis'
    Just _ -> Bottom
simplify (Or phis) =
  let phis' = filter (/= Bottom) (fmap simplify phis) in
  case find (== Top) phis' of
    Nothing ->
      case phis' of
        []    -> Bottom
        [phi] -> phi
        phis' -> Or phis'
    Just _ -> Top
simplify (Implies a b) =
  case (simplify a, simplify b) of
    (Top, b)    -> b
    (Bottom, b) -> Top
    (_, Top)    -> Top
    (a, Bottom) -> simplify (Not a)
    (a, b)      -> Implies a b
simplify (Not a) =
  case simplify a of
    Not a' -> a'
    Top    -> Bottom
    Bottom -> Top
    a      -> Not a
simplify Bottom = Bottom
simplify Top = Bottom
simplify (PropEq (Const v) v') | v == v' = Top
simplify (PropEq (Const v) v') = Bottom
simplify p@(PropEq _ _) = p
simplify p@(PropAtom _ _) = p
simplify (PropForall x phi) = PropForall x (simplify phi)
