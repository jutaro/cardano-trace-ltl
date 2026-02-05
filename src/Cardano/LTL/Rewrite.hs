{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE CPP          #-}
{-# LANGUAGE ViewPatterns #-}
module Cardano.LTL.Rewrite(
  rewriteHomogeneous,
  rewriteFragment,
  rewriteIdentity
  ) where

import           Cardano.Data.Strict
import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Lang.Internal.Fragment           (findAtoms,
                                                               normaliseFragment)
import           Cardano.LTL.Lang.Internal.GuardedFormula     (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula     as G
import           Cardano.LTL.Lang.Internal.HomogeneousFormula (HomogeneousFormula)
import qualified Cardano.LTL.Lang.Internal.HomogeneousFormula as H
import           Data.Set                                     (Set)
import qualified Data.Set                                     as Set
import           Prelude                                      hiding (lookup)

-- | Rewrite the formula by applying the fragment retraction & normalisation recursively.
rewriteFragment :: Ord ty => GuardedFormula ty -> GuardedFormula ty
rewriteFragment phi = go (findAtoms phi mempty) phi where
  go :: Ord ty => Set (Pair PropVarIdentifier PropValue) -> GuardedFormula ty -> GuardedFormula ty
  go _ (G.Next phi) = G.Next phi
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


fromGuarded :: GuardedFormula ty -> Maybe (HomogeneousFormula ty)
fromGuarded = go Set.empty where
  go :: Set PropVarIdentifier -> GuardedFormula ty -> Maybe (HomogeneousFormula ty)
  go _     (G.Next _)                  = Nothing
  go bound (G.And phi psi)             = H.And <$> go bound phi <*> go bound psi
  go bound (G.Or phi psi)              = H.Or <$> go bound phi <*> go bound psi
  go bound (G.Implies phi psi)         = H.Implies <$> go bound phi <*> go bound psi
  go bound (G.Not phi)                 = H.Not <$> go bound phi
  go _     G.Bottom                    = Just H.Bottom
  go _     G.Top                       = Just H.Top
  go _     (G.PropEq rel (Const v') v) = Just (H.PropEq rel (Const v') v)
  go bound (G.PropEq rel (Var x) v)
                | Set.member x bound   = Just (H.PropEq rel (Var x) v)
  go _     (G.PropEq _ (Var _) _)      = Nothing
  go bound (G.PropForall x phi)        = H.PropForall x <$> go (Set.insert x bound) phi

-- | Rewrite the formula by applying the decidability of equivalence of the homogeneous fragment.
rewriteHomogeneous :: GuardedFormula ty -> GuardedFormula ty
rewriteHomogeneous (fromGuarded -> Just g) =
  if H.interp g then G.Top else G.Bottom
rewriteHomogeneous phi = go phi where
  go :: GuardedFormula ty -> GuardedFormula ty
  go (G.Next phi)         = G.Next phi
  go (G.And phi psi)      = G.And (rewriteHomogeneous phi) (rewriteHomogeneous psi)
  go (G.Or phi psi)       = G.Or (rewriteHomogeneous phi) (rewriteHomogeneous psi)
  go (G.Implies phi psi)  = G.Implies (rewriteHomogeneous phi) (rewriteHomogeneous psi)
  go (G.Not phi)          = G.Not (go phi)
  go G.Bottom             = G.Bottom
  go G.Top                = G.Top
  go (G.PropEq rel t v)   = G.PropEq rel t v
  go (G.PropForall x phi) = G.PropForall x (go phi)


-- | Rewrites the formula by the following logical identities:
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
rewriteIdentity :: Eq ty => Formula ty -> Formula ty
rewriteIdentity (Forall k phi) =
  case rewriteIdentity phi of
    Top -> Top
    phi -> Forall k phi
rewriteIdentity (ForallN k phi) =
  case rewriteIdentity phi of
    Top -> Top
    phi -> ForallN k phi
rewriteIdentity (ExistsN k phi) =
  case rewriteIdentity phi of
    Bottom -> Bottom
    phi    -> ExistsN k phi
rewriteIdentity (Next phi) = Next (rewriteIdentity phi)
rewriteIdentity (NextN k phi) = NextN k (rewriteIdentity phi)
rewriteIdentity (UntilN k phi psi) =
  case rewriteIdentity psi of
    Top -> Top
    psi -> UntilN k (rewriteIdentity phi) psi
rewriteIdentity (And phi psi) =
  case (rewriteIdentity phi, rewriteIdentity psi) of
    (Bottom, _) -> Bottom
    (Top, psi)  -> psi
    (_, Bottom) -> Bottom
    (phi, Top)  -> phi
    (phi, psi)  -> And phi psi
rewriteIdentity (Or phi psi) =
  case (rewriteIdentity phi, rewriteIdentity psi) of
    (Bottom, psi) -> psi
    (Top, _)      -> Top
    (phi, Bottom) -> phi
    (_, Top)      -> Top
    (phi, psi)    -> Or phi psi
rewriteIdentity (Implies phi psi) =
  case (rewriteIdentity phi, rewriteIdentity psi) of
    (Top, psi)    -> psi
    (Bottom, _)   -> Top
    (_, Top)      -> Top
    (phi, Bottom) -> rewriteIdentity (Not phi)
    (phi, psi)    -> Implies phi psi
rewriteIdentity (Not phi) =
  case rewriteIdentity phi of
    Not phi' -> phi'
    Top      -> Bottom
    Bottom   -> Top
    phi      -> Not phi
rewriteIdentity Bottom = Bottom
rewriteIdentity Top = Top
rewriteIdentity (PropEq _ (Const v) v') | v == v' = Top
rewriteIdentity (PropEq _ (Const _) _) = Bottom
rewriteIdentity p@(PropEq {}) = p
rewriteIdentity p@(PropAtom {}) = p
rewriteIdentity (PropForall x phi) =
  case rewriteIdentity phi of
    Top    -> Top
    Bottom -> Bottom
    phi    -> PropForall x phi
