module Cardano.LTL.Lang.Internal.Fragment1(Frag1(..), not) where

import           Cardano.LTL.Lang.Formula (Relevance)
import           Prelude                  hiding (not)

-- | t ::= ☐ | ¬☐ | t ∧ t | t ∨ t | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Frag1 ty = Atom (Relevance ty)
              | NotAtom (Relevance ty)
              | And (Frag1 ty) (Frag1 ty)
              | Or (Frag1 ty) (Frag1 ty)
              | Top
              | Bottom

-- | ¬ t
not :: Frag1 ty -> Frag1 ty
not (Atom set)    = NotAtom set
not (NotAtom set) = Atom set
not (And a b)     = Or (not a) (not b)
not (Or a b)      = And (not a) (not b)
not Top           = Bottom
not Bottom        = Top
