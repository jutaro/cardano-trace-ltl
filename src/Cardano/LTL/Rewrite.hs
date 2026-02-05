{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE CPP          #-}
{-# LANGUAGE ViewPatterns #-}
module Cardano.LTL.Rewrite(
  rewriteHomogeneous,
  rewriteFragment,
  rewriteIdentity
  ) where

import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Lang.Internal.Fragment           (findAtoms,
                                                               normaliseFragment)
import           Cardano.LTL.Lang.Internal.GuardedFormula     (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula     as G
import qualified Cardano.LTL.Lang.Internal.HomogeneousFormula as H
import           Data.Set                                     (Set)
import           Prelude                                      hiding (lookup)

-- This file concerns applying rewrite rules to a formula.
-- The rewrite rules must be logical identities, hence all rewrites here produce logically equivalent formulas.

-- | Rewrite the formula by applying the fragment retraction & normalisation recursively.
rewriteFragment :: Ord ty => GuardedFormula ty -> GuardedFormula ty
rewriteFragment phi = go (findAtoms phi mempty) phi where
  go :: Ord ty => Set (PropVarIdentifier, PropValue) -> GuardedFormula ty -> GuardedFormula ty
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


-- | Rewrite the formula by applying the homogeneous fragment retraction & normalisation recursively.
rewriteHomogeneous :: GuardedFormula ty -> GuardedFormula ty
rewriteHomogeneous (H.retract -> Just g) =
  if H.eval g then G.Top else G.Bottom
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


-- | Rewrites the formula by the following logical identities recursively:
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
--   Additionally, unfolds base-cases of finite temporal operators.
rewriteIdentity :: Eq ty => Formula ty -> Formula ty
rewriteIdentity (Forall k phi) =
  case rewriteIdentity phi of
    Top -> Top
    phi -> Forall k phi
rewriteIdentity (ForallN 0 phi) = rewriteIdentity (unfoldForallN 0 phi)
rewriteIdentity (ForallN k phi) =
  case rewriteIdentity phi of
    Top -> Top
    phi -> ForallN k phi
rewriteIdentity (ExistsN 0 phi) = rewriteIdentity (unfoldExistsN 0 phi)
rewriteIdentity (ExistsN k phi) =
  case rewriteIdentity phi of
    Bottom -> Bottom
    phi    -> ExistsN k phi
rewriteIdentity (Next phi) = Next (rewriteIdentity phi)
rewriteIdentity (NextN 0 phi) = rewriteIdentity (unfoldNextN 0 phi)
rewriteIdentity (NextN k phi) = NextN k (rewriteIdentity phi)
rewriteIdentity (UntilN 0 phi psi) = rewriteIdentity (unfoldUntilN 0 phi psi)
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
