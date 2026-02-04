module Cardano.LTL.Lang.Internal.Fragment0(Frag0(..), andList, orList) where
import           Cardano.LTL.Lang.Formula (Relevance)

-- | t ::= ☐ | ¬ t | t ∧ t | t ∨ t | t ⇒ t | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Frag0 ty = Atom (Relevance ty)
              | Not (Frag0 ty)
              | And (Frag0 ty) (Frag0 ty)
              | Or (Frag0 ty) (Frag0 ty)
              | Implies (Frag0 ty) (Frag0 ty)
              | Top
              | Bottom

-- t₁ ∧ t₂ ∧ ... ∧ tₙ
andList :: [Frag0 ty] -> Frag0 ty
andList = foldl' And Top

-- t₁ ∨ t₂ ∨ ... ∨ tₙ
orList :: [Frag0 ty] -> Frag0 ty
orList = foldl' Or Bottom
