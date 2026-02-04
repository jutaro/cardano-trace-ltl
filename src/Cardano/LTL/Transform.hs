{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE CPP    #-}
{-# LANGUAGE ViewPatterns #-}
module Cardano.LTL.Transform(
    step
  , simplify
  , simplifyNext
  , simplifyFragment
  , simplifyHomogeneous
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
step (Forall k phi) s = G.And (step phi s) (G.Next True (NextN True k (Forall k phi)))
step (ForallN 0 phi) s = G.Top
step (ForallN k phi) s = G.And (step phi s) (G.Next True (ForallN (k - 1) phi))
step (ExistsN w 0 phi) s = G.Bottom
step (ExistsN w k phi) s = G.Or (step phi s) (G.Next w (ExistsN w (k - 1) phi))
step (Next w phi) _ = G.Next w phi
step (NextN _ 0 phi) s = step phi s
step (NextN w k phi) s = G.Next w (NextN w (k - 1) phi)
step (UntilN w 0 phi psi) s = G.Top
step (UntilN w k phi psi) s =
  G.Or (step psi s)
       (G.And
         (step phi s)
         (G.And
           (G.Not (step psi s))
           (G.Next w (UntilN w (k - 1) phi psi))
         )
       )
step (And phi psi) s = G.And (step phi s) (step psi s)
step (Or phi psi) s = G.Or (step phi s) (step psi s)
step (Implies phi psi) s = G.Implies (step phi s) (step psi s)
step (Not phi) s = G.Not (step phi s)
step Bottom _ = G.Bottom
step Top _ = G.Top
step (PropAtom c is) s | ofTy s c =
  G.and $ flip fmap (Set.toList is) $ \(PropConstraint key t) ->
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
terminate :: Formula a -> HomogeneousFormula
terminate (Forall _ _)             = H.Top
terminate (ForallN _ _)            = H.Top
terminate (ExistsN True _ _)       = H.Top
terminate (ExistsN False _ _)      = H.Bottom
terminate (NextN _ 0 phi)          = terminate phi
terminate (NextN True _ _)         = H.Top
terminate (NextN False _ _)        = H.Bottom
terminate (UntilN _ 0 _ psi)       = H.Top
terminate (UntilN True _ _ _)      = H.Top
terminate (UntilN False _ _ _)     = H.Bottom
terminate (PropAtom _ _)           = H.Bottom
terminate (Next True _)            = H.Top
terminate (Next False _)           = H.Bottom
terminate (And phi psi)            = H.And (terminate phi) (terminate psi)
terminate (Or phi psi)             = H.Or (terminate phi) (terminate psi)
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
  pushNext w (Forall k phi)        = G.Next w (Forall k phi)
  pushNext w (ForallN k phi)       = G.Next w (ForallN k phi)
  pushNext w (ExistsN w' k phi)    = G.Next w (ExistsN w' k phi)
  pushNext w (Next w' phi)         = G.Next w (Next w' phi)
  pushNext w (NextN _ 0 phi)       = pushNext w phi
  pushNext w (NextN w' k phi)      = G.Next w (NextN w' k phi)
  pushNext w (UntilN _ 0 _ psi)    = G.Top
  pushNext w (UntilN w' k phi psi) = G.Next w (UntilN w' k phi psi)
  pushNext w (And phi psi)         = G.And (pushNext w phi) (pushNext w psi)
  pushNext w (Or phi psi)          = G.Or (pushNext w phi) (pushNext w psi)
  pushNext w (Implies phi psi)     = G.Implies (pushNext w phi) (pushNext w psi)
  pushNext w (Not phi)             = G.Not (pushNext w phi)
  pushNext _ Bottom                = G.Bottom
  pushNext _ Top                   = G.Top
  pushNext _ (PropEq rel t v)      = G.PropEq rel t v
  pushNext w (PropAtom c cs)       = G.Next w (PropAtom c cs)
  pushNext w (PropForall x phi)    = G.PropForall x (pushNext w phi)
simplifyNext (G.And phi psi)       = G.And (simplifyNext phi) (simplifyNext psi)
simplifyNext (G.Or phi psi)        = G.Or (simplifyNext phi) (simplifyNext psi)
simplifyNext (G.Implies phi psi)   = G.Implies (simplifyNext phi) (simplifyNext psi)
simplifyNext (G.Not phi)          = G.Not (simplifyNext phi)
simplifyNext G.Bottom             = G.Bottom
simplifyNext G.Top                = G.Top
simplifyNext (G.PropEq rel t v)   = G.PropEq rel t v
simplifyNext (G.PropForall x phi) = G.PropForall x (simplifyNext phi)


-- | Applies the fragment retraction & normalisation recursively.
simplifyFragment :: Eq ty => GuardedFormula ty -> GuardedFormula ty
simplifyFragment phi = go (findAtoms phi mempty) phi where
  go :: Eq ty => Set (Pair PropVarIdentifier PropValue) -> GuardedFormula ty -> GuardedFormula ty
  go _ (G.Next w phi) = G.Next w phi
  go atoms (G.And phi psi) =
    normaliseFragment atoms (G.And (go atoms phi) (go atoms psi))
  go atoms (G.Or phi psi) =
    normaliseFragment atoms (G.Or (go atoms phi) (go atoms psi))
  go atoms (G.Implies phi psi) =
    normaliseFragment atoms (G.Implies (go atoms phi) (go atoms psi))
  go atoms (G.Not phi) =
    normaliseFragment atoms (G.Not (go atoms phi))
  go _ G.Bottom = G.Bottom
  go _ G.Top = G.Top
  go _ (G.PropEq rel t v) = G.PropEq rel t v
  go atoms (G.PropForall x phi) = G.PropForall x (go atoms phi)


fromGuarded :: GuardedFormula ty -> Maybe HomogeneousFormula
fromGuarded = go Set.empty where
  go :: Set PropVarIdentifier -> GuardedFormula ty -> Maybe HomogeneousFormula
  go bound (G.Next w phi)              = Nothing
  go bound (G.And phi psi)             = H.And <$> go bound phi <*> go bound psi
  go bound (G.Or phi psi)              = H.Or <$> go bound phi <*> go bound psi
  go bound (G.Implies phi psi)         = H.Implies <$> go bound phi <*> go bound psi
  go bound (G.Not phi)                 = H.Not <$> go bound phi
  go bound G.Bottom                    = Just H.Bottom
  go bound G.Top                       = Just H.Top
  go bound (G.PropEq rel (Const v') v) = Just (H.PropEq rel (Const v') v)
  go bound (G.PropEq rel (Var x) v)
                | Set.member x bound   = Just (H.PropEq rel (Var x) v)
  go bound (G.PropEq rel (Var x) _)    = Nothing
  go bound (G.PropForall x phi)        = H.PropForall x <$> go (Set.insert x bound) phi

simplifyHomogeneous' :: GuardedFormula ty -> GuardedFormula ty
simplifyHomogeneous' (G.Next w phi)       = G.Next w phi
simplifyHomogeneous' (G.And phi psi)      = G.And (simplifyHomogeneous phi) (simplifyHomogeneous psi)
simplifyHomogeneous' (G.Or phi psi)       = G.Or (simplifyHomogeneous phi) (simplifyHomogeneous psi)
simplifyHomogeneous' (G.Implies phi psi)  = G.Implies (simplifyHomogeneous phi) (simplifyHomogeneous psi)
simplifyHomogeneous' (G.Not phi)          = G.Not (simplifyHomogeneous' phi)
simplifyHomogeneous' G.Bottom             = G.Bottom
simplifyHomogeneous' G.Top                = G.Top
simplifyHomogeneous' (G.PropEq rel t v)   = G.PropEq rel t v
simplifyHomogeneous' (G.PropForall x phi) = G.PropForall x (simplifyHomogeneous' phi)

simplifyHomogeneous :: GuardedFormula ty -> GuardedFormula ty
simplifyHomogeneous (fromGuarded -> Just g) =
  if H.interp g then G.Top else G.Bottom
simplifyHomogeneous phi = simplifyHomogeneous' phi

-- | Applies the following equivalences recursively:
--   ☐ ᪲ₖ ⊤ = ⊤
--   ☐ᵏ ⊤ = ⊤
--   ♢ᵏ ⊥ = ⊥
--   φ |ᵏ ⊤ = ⊤
--   φ ∧ ⊤ = φ
--   ⊤ ∧ φ = φ
--   φ ∧ ⊥ = ⊥
--   ⊥ ∧ φ = ⊥
--   ⊤ ∨ φ = ⊤
--   φ ∨ ⊤ = ⊤
--   ⊥ ∨ φ = φ
--   φ ∨ ⊥ = φ
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
--   Assumes the formula has been stepped through.
simplify :: Eq ty => Formula ty -> Formula ty
simplify (Forall k phi) =
  case simplify phi of
    Top    -> Top
    phi    -> Forall k phi
simplify (ForallN k phi) =
  case simplify phi of
    Top    -> Top
    phi    -> ForallN k phi
simplify (ExistsN w k phi) =
  case simplify phi of
    Bottom -> Bottom
    phi    -> ExistsN w k phi
simplify (Next w phi) = Next w (simplify phi)
simplify (NextN w k phi) = NextN w k (simplify phi)
simplify (UntilN w k phi psi) =
  case simplify psi of
    Top    -> Top
    psi    -> UntilN w k (simplify phi) psi
simplify (And phi psi) =
  case (simplify phi, simplify psi) of
    (Bottom, psi) -> Bottom
    (Top, psi) -> psi
    (phi, Bottom) -> Bottom
    (phi, Top) -> phi
    (phi, psi) -> And phi psi
simplify (Or phi psi) =
  case (simplify phi, simplify psi) of
    (Bottom, psi) -> psi
    (Top, psi) -> Top
    (phi, Bottom) -> phi
    (phi, Top) -> Top
    (phi, psi) -> Or phi psi
simplify (Implies phi psi) =
  case (simplify phi, simplify psi) of
    (Top, psi)    -> psi
    (Bottom, _)   -> Top
    (_, Top)      -> Top
    (phi, Bottom) -> simplify (Not phi)
    (phi, psi)    -> Implies phi psi
simplify (Not phi) =
  case simplify phi of
    Not phi' -> phi'
    Top    -> Bottom
    Bottom -> Top
    phi    -> Not phi
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
