{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang.Internal.HomogeneousFormula (
    HomogeneousFormula(..)
  , toGuardedFormula, toFormula) where

import           Cardano.LTL.Lang.Formula                 (Formula, PropTerm,
                                                           PropValue,
                                                           PropVarIdentifier)
import qualified Cardano.LTL.Lang.Formula                 as F
import           Cardano.LTL.Lang.Internal.GuardedFormula (GuardedFormula)
import qualified Cardano.LTL.Lang.Internal.GuardedFormula as G
import qualified Data.Map                                 as Map
import           Data.Map.Strict                          (Map)
import           Data.Set                                 (Set, union)
import qualified Data.Set                                 as Set
import           Data.Text                                (Text)

-- | A `Formula` with no temporal operators.
data HomogeneousFormula ty =
   ------------ Connective -------------
     Or [HomogeneousFormula ty]
   | And [HomogeneousFormula ty]
   | Not (HomogeneousFormula ty)
   | Implies (HomogeneousFormula ty) (HomogeneousFormula ty)
   | Top
   | Bottom
   -------------------------------------


   ----------- Event property ----------
   | PropForall PropVarIdentifier (HomogeneousFormula ty)
   | PropEq PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------

toGuardedFormula :: HomogeneousFormula ty -> GuardedFormula ty
toGuardedFormula (And phis)         = G.And (fmap toGuardedFormula phis)
toGuardedFormula (Or phis)          = G.Or (fmap toGuardedFormula phis)
toGuardedFormula (Implies a b)      = G.Implies (toGuardedFormula a) (toGuardedFormula b)
toGuardedFormula (Not a)            = G.Not (toGuardedFormula a)
toGuardedFormula Bottom             = G.Bottom
toGuardedFormula Top                = G.Top
toGuardedFormula (PropForall x phi) = G.PropForall x (toGuardedFormula phi)
toGuardedFormula (PropEq a b)       = G.PropEq a b

toFormula :: HomogeneousFormula ty -> Formula ty
toFormula (And phis)         = F.And (fmap toFormula phis)
toFormula (Or phis)          = F.Or (fmap toFormula phis)
toFormula (Implies a b)      = F.Implies (toFormula a) (toFormula b)
toFormula (Not a)            = F.Not (toFormula a)
toFormula Bottom             = F.Bottom
toFormula Top                = F.Top
toFormula (PropForall x phi) = F.PropForall x (toFormula phi)
toFormula (PropEq a b)       = F.PropEq a b
