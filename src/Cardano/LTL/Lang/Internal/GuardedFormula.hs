{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang.Internal.GuardedFormula (
    GuardedFormula(..)
  , toFormula
  , forward) where

import           Cardano.LTL.Lang.Formula (Formula, PropTerm, PropValue,
                                           PropVarIdentifier)
import qualified Cardano.LTL.Lang.Formula as F
import qualified Data.Map                 as Map
import           Data.Map.Strict          (Map)
import           Data.Set                 (Set, union)
import qualified Data.Set                 as Set
import           Data.Text                (Text)

-- | A `Formula` where all temporal operators are guarded by a "◯".
data GuardedFormula ty =
   ------------ Temporal -------------
     Next Bool (Formula ty)
   -------------------------------------


   ------------ Connective -------------
   | Or [GuardedFormula ty]
   | And [GuardedFormula ty]
   | Not (GuardedFormula ty)
   | Implies (GuardedFormula ty) (GuardedFormula ty)
   | Top
   | Bottom
   -------------------------------------


   ----------- Event property ----------
   | PropForall PropVarIdentifier (GuardedFormula ty)
   | PropEq PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------

-- | Embed `GuardedFormula` into `Formula`
toFormula :: GuardedFormula ty -> Formula ty
toFormula (Next w phi)       = F.Next w phi
toFormula (And phis)         = F.And (fmap toFormula phis)
toFormula (Or phis)          = F.Or (fmap toFormula phis)
toFormula (Implies a b)      = F.Implies (toFormula a) (toFormula b)
toFormula (Not a)            = F.Not (toFormula a)
toFormula Bottom             = F.Bottom
toFormula Top                = F.Top
toFormula (PropForall x phi) = F.PropForall x (toFormula phi)
toFormula (PropEq a b)       = F.PropEq a b

-- | Peel off one layer of "◯" in `GuardedFormula`, landing in `Formula`.
forward :: GuardedFormula ty -> Formula ty
forward (Next _ phi)       = phi
forward (And phis)         = F.And (fmap forward phis)
forward (Or phis)          = F.Or (fmap forward phis)
forward (Implies phi psi)  = F.Implies (forward phi) (forward psi)
forward (Not phi)          = F.Not (forward phi)
forward Bottom             = F.Bottom
forward Top                = F.Top
forward (PropForall x phi) = F.PropForall x (forward phi)
forward (PropEq a b)       = F.PropEq a b
