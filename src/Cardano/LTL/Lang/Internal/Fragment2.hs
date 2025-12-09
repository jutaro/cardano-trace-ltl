module Cardano.LTL.Lang.Internal.Fragment2(Frag2(..), and, or) where

import Prelude hiding (and, or)

-- | t ::= ☐ | ¬☐ | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Frag2 = Atom | NotAtom | Top | Bottom

-- | t₀ ∧ t₁
and :: Frag2 -> Frag2 -> Frag2
and Atom    Atom       = Atom
and Atom    NotAtom    = Bottom
and Atom    Bottom     = Bottom
and Atom    Top        = Atom
and NotAtom Atom       = Bottom
and NotAtom NotAtom    = NotAtom
and NotAtom Top        = NotAtom
and NotAtom Bottom     = Bottom
and Top     b          = b
and Bottom  b          = Bottom

-- | t₀ ∨ t₁
or :: Frag2 -> Frag2 -> Frag2
or Atom    Atom       = Atom
or Atom    NotAtom    = Top
or Atom    Bottom     = Atom
or Atom    Top        = Top
or NotAtom Atom       = Top
or NotAtom NotAtom    = NotAtom
or NotAtom Top        = Top
or NotAtom Bottom     = NotAtom
or Bottom  b          = b
or Top     b          = Top
