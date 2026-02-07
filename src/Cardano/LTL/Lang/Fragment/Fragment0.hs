module Cardano.LTL.Lang.Fragment.Fragment0(Fragment0(..), andList, orList) where
import           Cardano.LTL.Lang.Formula (Relevance)

-- | t ::= ☐ | ¬ t | t ∧ t | t ∨ t | t ⇒ t | ⊤ | ⊥
--   NOTE: "☐" here stands for "atom".
data Fragment0 ty = Atom (Relevance ty)
                  | Not (Fragment0 ty)
                  | And (Fragment0 ty) (Fragment0 ty)
                  | Or (Fragment0 ty) (Fragment0 ty)
                  | Implies (Fragment0 ty) (Fragment0 ty)
                  | Top
                  | Bottom

-- t₁ ∧ t₂ ∧ ... ∧ tₙ
andList :: [Fragment0 ty] -> Fragment0 ty
andList = foldl' And Top

-- t₁ ∨ t₂ ∨ ... ∨ tₙ
orList :: [Fragment0 ty] -> Fragment0 ty
orList = foldl' Or Bottom
