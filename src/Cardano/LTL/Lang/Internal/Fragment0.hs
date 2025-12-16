module Cardano.LTL.Lang.Internal.Fragment0(Frag0(..), andList, orList) where
import           Data.Set (Set)

-- | t ::= ☐ | ¬ t | t ∧ t | t ∨ t | t ⇒ t | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Frag0 = Atom (Set Int)
           | Not Frag0
           | And Frag0 Frag0
           | Or Frag0 Frag0
           | Implies Frag0 Frag0
           | Top
           | Bottom

-- t₁ ∧ t₂ ∧ ... ∧ tₙ
andList :: [Frag0] -> Frag0
andList = foldl' And Top

-- t₁ ∨ t₂ ∨ ... ∨ tₙ
orList :: [Frag0] -> Frag0
orList = foldl' Or Bottom
