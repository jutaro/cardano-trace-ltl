module Cardano.LTL.Lang.Internal.Fragment2(Frag2(..), and, or) where

import           Data.Set (Set, union)
import           Prelude  hiding (and, or)

-- | t ::= ☐ | ¬☐ | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Frag2 = Atom (Set Int) | NotAtom (Set Int) | Top | Bottom

-- | t₀ ∧ t₁
and :: Frag2 -> Frag2 -> Frag2
and (Atom ty) (Atom ty')       = Atom (ty `union` ty')
and (Atom _) (NotAtom _)       = Bottom
and (Atom _) Bottom            = Bottom
and (Atom ty) Top              = Atom ty
and (NotAtom _) (Atom _)       = Bottom
and (NotAtom ty) (NotAtom ty') = NotAtom (ty `union` ty')
and (NotAtom ty) Top           = NotAtom ty
and (NotAtom _) Bottom         = Bottom
and Top     b                  = b
and Bottom  b                  = Bottom

-- | t₀ ∨ t₁
or :: Frag2 -> Frag2 -> Frag2
or (Atom ty) (Atom ty')       = Atom (ty `union` ty')
or (Atom _) (NotAtom _)       = Top
or (Atom ty) Bottom           = Atom ty
or (Atom _) Top               = Top
or (NotAtom _) (Atom _)       = Top
or (NotAtom ty) (NotAtom ty') = NotAtom (ty `union` ty')
or (NotAtom _) Top            = Top
or (NotAtom ty) Bottom        = NotAtom ty
or Bottom  b                  = b
or Top     b                  = Top
