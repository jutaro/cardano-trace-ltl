{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang.Internal.GuardedFormula (
    GuardedFormula(..)
  , and
  , toFormula
  , forward) where

import           Cardano.LTL.Lang.Formula (EventIndex, Formula, PropTerm,
                                           PropValue, PropVarIdentifier)
import qualified Cardano.LTL.Lang.Formula as F
import qualified Data.Map                 as Map
import           Data.Map.Strict          (Map)
import           Data.Set                 (Set, union)
import qualified Data.Set                 as Set
import           Data.Text                (Text)
import           Prelude                  hiding (and)

-- | A `Formula` where all temporal operators are guarded by a "◯".
data GuardedFormula ty =
   ------------ Temporal -------------
     Next Bool (Formula ty)
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
   | PropEq (Set EventIndex) PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------

and :: [GuardedFormula ty] -> GuardedFormula ty
and []           = Top
and [phi]        = phi
and (phi : phis) = And phi (and phis)

-- | Embed `GuardedFormula` into `Formula`
toFormula :: GuardedFormula ty -> Formula ty
toFormula (Next w phi)       = F.Next w phi
toFormula (And a b)          = F.And (toFormula a) (toFormula b)
toFormula (Or a b)           = F.Or (toFormula a) (toFormula b)
toFormula (Implies a b)      = F.Implies (toFormula a) (toFormula b)
toFormula (Not a)            = F.Not (toFormula a)
toFormula Bottom             = F.Bottom
toFormula Top                = F.Top
toFormula (PropForall x phi) = F.PropForall x (toFormula phi)
toFormula (PropEq e a b)     = F.PropEq e a b

-- | Peel off one layer of "◯" in `GuardedFormula`, landing in `Formula`.
forward :: GuardedFormula ty -> Formula ty
forward (Next _ phi)       = phi
forward (And phi psi)      = F.And (forward phi) (forward psi)
forward (Or phi psi)       = F.Or (forward phi) (forward psi)
forward (Implies phi psi)  = F.Implies (forward phi) (forward psi)
forward (Not phi)          = F.Not (forward phi)
forward Bottom             = F.Bottom
forward Top                = F.Top
forward (PropForall x phi) = F.PropForall x (forward phi)
forward (PropEq e a b)     = F.PropEq e a b
