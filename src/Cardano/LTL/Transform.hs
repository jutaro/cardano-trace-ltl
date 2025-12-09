{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Transform(
    step
  , end
  , Relevance(..)
  , simplify
  , simplifyNext
  , simplifyFragment
  , terminate
  ) where

import           Cardano.Data.Strict
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Lang.Internal.Fragment           (findAtoms,
                                                               normaliseFragment)
import           Cardano.LTL.Lang.Internal.GuardedFormula     (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula     as G
import           Cardano.LTL.Lang.Internal.HomogeneousFormula (HomogeneousFormula)
import qualified Cardano.LTL.Lang.Internal.HomogeneousFormula as H
import           Cardano.LTL.Occurs                           (occursFormula)
import           Cardano.LTL.Subst                            (substFormula)
import           Data.List                                    hiding (lookup)
import           Data.Map.Strict                              (lookup)
import           Data.Set                                     (Set)
import qualified Data.Set                                     as Set
import           Data.Text                                    (unpack)
import           Prelude                                      hiding (lookup)

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

-- | Fast forwards the `Formula` through the given event.
-- | Returns an equivalent `GuardedFormula` and whether the event is "relevant".
-- | An event is relevant in a formula iff the formula contains an atom of that event type "now".
step :: (Event m ty, Eq ty) => Formula ty -> m -> Relevance (GuardedFormula ty)
step (Forall phi) s = (\x -> G.And [x, G.Next True (Forall phi)]) <$> step phi s
step (Exists phi) s = (\x -> G.Or [x, G.Next False (Exists phi)]) <$> step phi s
step (Next w phi) _ = irrelevant (G.Next w phi)
step (RepeatNext _ 0 phi) s = step phi s
step (RepeatNext w k phi) s = (\x -> G.Or [x, G.Next w (RepeatNext w (k - 1) phi)]) <$> step phi s
step (Until w phi psi) s = (\x y -> G.Or [x, G.And [y, G.Next w (Until w phi psi)]]) <$> step psi s <*> step phi s
step (And phis) s = G.And <$> traverse (`step` s) phis
step (Or phis) s = G.Or <$> traverse (`step` s) phis
step (Implies phi psi) s = G.Implies <$> step phi s <*> step psi s
step (Not phi) s = G.Not <$> step phi s
step Bottom _ = irrelevant G.Bottom
step Top _ = irrelevant G.Top
step (PropAtom c is) s | ty s c =
  relevant $ G.And $ flip fmap (Set.toList is) $ \(PropConstraint key t) ->
    case lookup key (props s c) of
      Just v  -> G.PropEq t v
      -- NOTE: Shall we have a config option for either crashing hard or returning ⊥ in case there is no such key?
      Nothing -> G.Bottom
step (PropForall x phi) s = G.PropForall x <$> step phi s
step (PropAtom _ _) _ = irrelevant G.Bottom
step (PropEq a b) _ = irrelevant $ G.PropEq a b

-- | Assume that no more temporal events will follow and homogenise the formula.
terminate :: Formula a -> HomogeneousFormula a
terminate (Forall _)               = H.Top
terminate (Exists _)               = H.Bottom
terminate (RepeatNext True _ _)    = H.Top
terminate (RepeatNext False 0 phi) = terminate phi
terminate (RepeatNext False _ _)   = H.Bottom
terminate (Until True _ _)         = H.Top
terminate (Until False _ _)        = H.Bottom
terminate (PropAtom _ _)           = H.Bottom
terminate (Next True _)            = H.Top
terminate (Next False _)           = H.Bottom
terminate (And phis)               = H.And (fmap terminate phis)
terminate (Or phis)                = H.Or (fmap terminate phis)
terminate (Implies phi psi)        = H.Implies (terminate phi) (terminate psi)
terminate (Not phi)                = H.Not (terminate phi)
terminate Bottom                   = H.Bottom
terminate Top                      = H.Top
terminate (PropForall x phi)       = H.PropForall x (terminate phi)
terminate (PropEq a b)             = H.PropEq a b

-- | Check if the formula is a tautology, assuming the end of timeline.
--   The check is not complete. We conservatively check: (∀x. φ) is a tautology if (x ∉ FV(φ)) ∧ φ is a tautology.
end :: Formula a -> Bool
end (Forall _)            = True
end (Exists _)            = False
end (Next w _)            = w
end (RepeatNext _ 0 phi)  = end phi
end (RepeatNext w _ _)    = w
end (Until w _ _)         = w
end (And phis)            = foldl' (&&) True (fmap end phis)
end (Or phis)             = foldl' (||) False (fmap end phis)
end (Implies phi psi)     = not (end phi) || end psi
end (Not phi)             = not (end phi)
end Bottom                = False
end Top                   = True
end (PropAtom _ _)        = False
end (PropForall x phi)    = not (occursFormula x phi) && end phi
end (PropEq (Const v) v') = v == v'
end (PropEq (Var x) _)    = error $ "Encountered a var: " <> unpack x

-- | ◯ (φ ∨ ψ) = ◯ φ ∨ ◯ ψ
-- | ◯ (φ ∧ ψ) = ◯ φ ∧ ◯ ψ
-- | ◯ (φ ∨ ψ) = ◯ φ ∨ ◯ ψ
-- | ◯ (φ ⇒ ψ) = ◯ φ ⇒ ◯ ψ
-- | ◯ (¬ φ) = ¬ (◯ φ)
-- | ◯ ⊤ = ⊤
-- | ◯ ⊥ = ⊥
-- | ◯ (x = v) = (x = v)
-- | ◯ (∀x. φ) = ∀x. ◯ φ
simplifyNext :: GuardedFormula ty -> GuardedFormula ty
simplifyNext (G.Next w phi)       = pushNext w phi where
  pushNext :: Bool -> Formula ty -> GuardedFormula ty
  pushNext w (Forall phi)          = G.Next w (Forall phi)
  pushNext w (Exists phi)          = G.Next w (Exists phi)
  pushNext w (Next w' phi)         = G.Next w (Next w' phi)
  pushNext w (RepeatNext w' k phi) = G.Next w (RepeatNext w' k phi)
  pushNext w (Until w' phi psi)    = G.Next w (Until w' phi psi)
  pushNext w (And phis)            = G.And (fmap (pushNext w) phis)
  pushNext w (Or phis)             = G.Or (fmap (pushNext w) phis)
  pushNext w (Implies a b)         = G.Implies (pushNext w a) (pushNext w b)
  pushNext w (Not a)               = G.Not (pushNext w a)
  pushNext _ Bottom                = G.Bottom
  pushNext _ Top                   = G.Top
  pushNext _ (PropEq a b)          = G.PropEq a b
  pushNext w (PropAtom a b)        = G.Next w (PropAtom a b)
  pushNext w (PropForall x phi)    = G.PropForall x (pushNext w phi)
simplifyNext (G.And phis)         = G.And (fmap simplifyNext phis)
simplifyNext (G.Or phis)          = G.Or (fmap simplifyNext phis)
simplifyNext (G.Implies a b)      = G.Implies (simplifyNext a) (simplifyNext b)
simplifyNext (G.Not phi)          = G.Not (simplifyNext phi)
simplifyNext G.Bottom             = G.Bottom
simplifyNext G.Top                = G.Top
simplifyNext (G.PropEq a b)       = G.PropEq a b
simplifyNext (G.PropForall x phi) = G.PropForall x (simplifyNext phi)


-- | Applies the fragment retraction & normalisation recursively.
simplifyFragment :: Ord ty => GuardedFormula ty -> GuardedFormula ty
simplifyFragment phi = go (findAtoms phi mempty) phi where
  go :: Ord ty => Set (Pair PropVarIdentifier PropValue) -> GuardedFormula ty -> GuardedFormula ty
  go _ (G.Next w phi) = G.Next w phi
  go atoms (G.And phis) =
    let phis' = fmap (go atoms) phis in
    normaliseFragment atoms (G.And phis')
  go atoms (G.Or phis) =
    let phis' = fmap (go atoms) phis in
    normaliseFragment atoms (G.Or phis')
  go atoms (G.Implies a b) =
    let a' = go atoms a
        b' = go atoms b
    in
    normaliseFragment atoms (G.Implies a' b')
  go atoms (G.Not phi) =
    let phi' = go atoms phi in
    normaliseFragment atoms (G.Not phi')
  go _ G.Bottom = G.Bottom
  go _ G.Top = G.Top
  go _ (G.PropEq a b) = G.PropEq a b
  go atoms (G.PropForall x phi) = G.PropForall x (go atoms phi)

-- | Applies the following equivalences recursively:
--   ☐ ⊤ = ⊤
--   ☐ ⊥ = ⊥
--   ♢ ⊤ = ⊤
--   ♢ ⊥ = ⊥
--   φ | ⊤ = ⊤
--   φ | ⊥ = φ
--   (∧) [φ₁, ..., ⊤, ..., φₙ] = (∧) [φ₁, ..., φₙ]
--   (∧) [φ₁, ..., ⊥, ..., φₙ] = ⊥
--   (∧) [] = ⊤
--   (∧) [φ] = φ
--   (∨) [φ₁, ..., ⊤, ..., φₙ] = ⊤
--   (∨) [φ₁, ..., ⊥, ..., φₙ] = (∨) [φ₁, ..., φₙ]
--   (∨) [] = ⊥
--   (∨) [φ] = φ
--   ⊤ ⇒ φ = φ
--   ⊥ ⇒ φ = ⊤
--   φ ⇒ ⊤ = ⊤
--   φ ⇒ ⊥ = ¬ φ
--   ¬ (¬ φ) = φ
--   ¬ ⊥ = ⊤
--   ¬ ⊤ = ⊥
--   (v = v') = ⊤ where v = v'
--   (v = v') = ⊥ where v ≠ v'
--   ∀x. ⊤ = ⊤
--   ∀x. ⊥ = ⊥
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
simplify Top = Top
simplify (PropEq (Const v) v') | v == v' = Top
simplify (PropEq (Const v) v') = Bottom
simplify p@(PropEq _ _) = p
simplify p@(PropAtom _ _) = p
simplify (PropForall x phi) =
  case simplify phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> PropForall x phi
