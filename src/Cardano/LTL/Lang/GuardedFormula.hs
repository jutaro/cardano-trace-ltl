{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang.GuardedFormula (
    GuardedFormula(..)
  , and
  , toFormula
  , forward) where

import           Cardano.LTL.Lang.Formula (Formula, PropTerm,
                                           PropValue, PropVarIdentifier, Relevance)
import qualified Cardano.LTL.Lang.Formula as F
import           Prelude                  hiding (and)

-- | A `Formula` where all temporal operators are guarded by a "◯".
data GuardedFormula ty =
   ------------ Temporal -------------
     Next (Formula ty)
   -------------------------------------


   ------------ Connective -------------
   | Or (GuardedFormula ty) (GuardedFormula ty)
   | And (GuardedFormula ty) (GuardedFormula ty)
   | Not (GuardedFormula ty)
   | Implies (GuardedFormula ty) (GuardedFormula ty)
   | Top
   | Bottom
   -------------------------------------


   ----------- Event property ----------
   | PropForall PropVarIdentifier (GuardedFormula ty)
   | PropEq (Relevance ty) PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------

and :: [GuardedFormula ty] -> GuardedFormula ty
and []           = Top
and [phi]        = phi
and (phi : phis) = And phi (and phis)

-- | Embed `GuardedFormula` into `Formula`
toFormula :: GuardedFormula ty -> Formula ty
toFormula (Next phi)         = F.Next phi
toFormula (And phi psi)      = F.And (toFormula phi) (toFormula psi)
toFormula (Or phi psi)       = F.Or (toFormula phi) (toFormula psi)
toFormula (Implies phi psi)  = F.Implies (toFormula phi) (toFormula psi)
toFormula (Not phi)          = F.Not (toFormula phi)
toFormula Bottom             = F.Bottom
toFormula Top                = F.Top
toFormula (PropForall x phi) = F.PropForall x (toFormula phi)
toFormula (PropEq e t v)     = F.PropEq e t v

-- | Peel off one layer of "◯" in `GuardedFormula`, landing in `Formula`.
forward :: GuardedFormula ty -> Formula ty
forward (Next phi)         = phi
forward (And phi psi)      = F.And (forward phi) (forward psi)
forward (Or phi psi)       = F.Or (forward phi) (forward psi)
forward (Implies phi psi)  = F.Implies (forward phi) (forward psi)
forward (Not phi)          = F.Not (forward phi)
forward Bottom             = F.Bottom
forward Top                = F.Top
forward (PropForall x phi) = F.PropForall x (forward phi)
forward (PropEq e t v)     = F.PropEq e t v
