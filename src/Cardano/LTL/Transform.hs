{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE CPP    #-}
module Cardano.LTL.Transform(
    step
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

-- | Evaluates "now" of the `Formula` at the given event.
--   Returns an equivalent `GuardedFormula`.
step :: (Event event ty, Eq ty) => Formula ty -> event -> GuardedFormula ty
step (Forall phi) s = G.And [step phi s, G.Next True (Forall phi)]
step (ForallN 0 phi) s = G.Top
step (ForallN k phi) s = G.And [step phi s, G.Next True (ForallN (k - 1) phi)]
step (ExistsN w 0 phi) s = G.Bottom
step (ExistsN w k phi) s = G.Or [step phi s, G.Next w (ExistsN w (k - 1) phi)]
step (Next w phi) _ = G.Next w phi
step (NextN _ 0 phi) s = step phi s
step (NextN w k phi) s = G.Next w (NextN w (k - 1) phi)
step (UntilN w 0 phi psi) s = step psi s
step (UntilN w k phi psi) s = G.Or [step psi s, G.And [step phi s, G.Not (step psi s), G.Next w (UntilN w (k - 1) phi psi)]]
step (And phis) s = G.And $ fmap (`step` s) phis
step (Or phis) s = G.Or $ fmap (`step` s) phis
step (Implies phi psi) s = G.Implies (step phi s) (step psi s)
step (Not phi) s = G.Not (step phi s)
step Bottom _ = G.Bottom
step Top _ = G.Top
step (PropAtom c is) s | ofTy s c =
  G.And $ flip fmap (Set.toList is) $ \(PropConstraint key t) ->
    case lookup key (props s c) of
      Just v  -> G.PropEq (Set.singleton (index s)) t v
      Nothing ->
#ifdef CRITICAL_ERROR_ON_MISSING_KEY
        error $ "Missing key: " <> unpack key
#else
        G.Bottom
#endif
step (PropAtom {}) _ = G.Bottom
step (PropForall x phi) s = G.PropForall x (step phi s)
step (PropEq rel a b) _ = G.PropEq rel a b

-- | Assume that no more temporal events will follow and homogenise the formula.
terminate :: Formula a -> HomogeneousFormula a
terminate (Forall _)               = H.Top
terminate (ForallN _ _)            = H.Top
terminate (ExistsN True _ _)       = H.Top
terminate (ExistsN False _ _)      = H.Bottom
terminate (NextN _ 0 phi)          = terminate phi
terminate (NextN True _ _)         = H.Top
terminate (NextN False _ _)        = H.Bottom
terminate (UntilN _ 0 _ psi)       = terminate psi
terminate (UntilN True _ _ _)      = H.Top
terminate (UntilN False _ _ _)     = H.Bottom
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
terminate (PropEq rel a b)         = H.PropEq rel a b

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
  pushNext w (ForallN k phi)       = G.Next w (ForallN k phi)
  pushNext w (ExistsN w' k phi)    = G.Next w (ExistsN w' k phi)
  pushNext w (Next w' phi)         = G.Next w (Next w' phi)
  pushNext w (NextN _ 0 phi)       = pushNext w phi
  pushNext w (NextN w' k phi)      = G.Next w (NextN w' k phi)
  pushNext w (UntilN _ 0 _ psi)    = pushNext w psi
  pushNext w (UntilN w' k phi psi) = G.Next w (UntilN w' k phi psi)
  pushNext w (And phis)            = G.And (fmap (pushNext w) phis)
  pushNext w (Or phis)             = G.Or (fmap (pushNext w) phis)
  pushNext w (Implies a b)         = G.Implies (pushNext w a) (pushNext w b)
  pushNext w (Not a)               = G.Not (pushNext w a)
  pushNext _ Bottom                = G.Bottom
  pushNext _ Top                   = G.Top
  pushNext _ (PropEq rel a b)      = G.PropEq rel a b
  pushNext w (PropAtom c a)        = G.Next w (PropAtom c a)
  pushNext w (PropForall x phi)    = G.PropForall x (pushNext w phi)
simplifyNext (G.And phis)         = G.And (fmap simplifyNext phis)
simplifyNext (G.Or phis)          = G.Or (fmap simplifyNext phis)
simplifyNext (G.Implies a b)      = G.Implies (simplifyNext a) (simplifyNext b)
simplifyNext (G.Not phi)          = G.Not (simplifyNext phi)
simplifyNext G.Bottom             = G.Bottom
simplifyNext G.Top                = G.Top
simplifyNext (G.PropEq rel a b)   = G.PropEq rel a b
simplifyNext (G.PropForall x phi) = G.PropForall x (simplifyNext phi)


-- | Applies the fragment retraction & normalisation recursively.
simplifyFragment :: Eq ty => GuardedFormula ty -> GuardedFormula ty
simplifyFragment phi = go (findAtoms phi mempty) phi where
  go :: Eq ty => Set (Pair PropVarIdentifier PropValue) -> GuardedFormula ty -> GuardedFormula ty
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
  go _ (G.PropEq rel a b) = G.PropEq rel a b
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
simplify (ForallN 0 phi) = Top
simplify (ForallN k phi) =
  case simplify phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> ForallN k phi
simplify (ExistsN w 0 phi) = Bottom
simplify (ExistsN w k phi) =
  case simplify phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> ExistsN w k phi
simplify (Next w phi) = Next w (simplify phi)
simplify (NextN w 0 phi) = simplify phi
simplify (NextN w k phi) = NextN w k (simplify phi)
simplify (UntilN _ 0 phi psi) = simplify psi
simplify (UntilN w k phi psi) =
  case simplify psi of
    Top    -> Top
    psi    -> UntilN w k (simplify phi) psi
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
simplify (PropEq _ (Const v) v') | v == v' = Top
simplify (PropEq _ (Const v) v') = Bottom
simplify p@(PropEq {}) = p
simplify p@(PropAtom {}) = p
simplify (PropForall x phi) =
  case simplify phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> PropForall x phi
