module Cardano.LTL.Lang.Internal.Fragment1(Frag1(..), not) where

import           Cardano.LTL.Lang.Formula (EventIndex)
import           Data.Set                 (Set)
import           Prelude                  hiding (not)

-- | t ::= ☐ | ¬☐ | t ∧ t | t ∨ t | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Frag1 = Atom (Set EventIndex)
           | NotAtom (Set EventIndex)
           | And Frag1 Frag1
           | Or Frag1 Frag1
           | Top
           | Bottom

-- ¬ t
not :: Frag1 -> Frag1
not (Atom set)    = NotAtom set
not (NotAtom set) = Atom set
not (And a b)     = Or (not a) (not b)
not (Or a b)      = And (not a) (not b)
not Top           = Bottom
not Bottom        = Top
