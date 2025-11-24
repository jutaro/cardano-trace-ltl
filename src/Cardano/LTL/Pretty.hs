module Cardano.LTL.Pretty (
    Lvl(..)
  , prettyPropValue
  , prettyPropTerm
  , prettyPropConstraint
  , prettyPropConstraints
  , prettyFormula) where

import           Cardano.LTL.Lang
import           Data.List        (foldl', intercalate)
import qualified Data.Set         as Set

data Lvl = Z | O deriving (Show, Eq, Ord)

-- | Add parentheses when an inner precedence exceeds the outer one.
surround :: Lvl -> Lvl -> String -> String
surround outer inner str | outer <= inner = str
surround _ _ str = "(" <> str <> ")"

-- | Mark a connective as weak when requested.
weak :: Bool -> String -> String
weak True x  = x <> "˜"
weak False x = x

-- | Render a property value.
prettyPropValue :: PropValue -> String
prettyPropValue (IntValue i)    = show i
prettyPropValue (StringValue x) = x

-- | Render a property term.
prettyPropTerm :: PropTerm -> String
prettyPropTerm (Var x)     = x
prettyPropTerm (Const idx) = prettyPropValue idx

-- | Render a single property constraint.
prettyPropConstraint :: PropConstraint -> String
prettyPropConstraint (PropConstraint k v) = show k <> " = " <> prettyPropTerm v

-- | Render a list of property constraints.
prettyPropConstraints :: [PropConstraint] -> String
prettyPropConstraints = intercalate ", " . fmap prettyPropConstraint

-- | Pretty-print a full formula using unicode operators.
prettyFormula :: Show a => Formula a -> Lvl -> String
prettyFormula (Forall phi) lvl = surround lvl Z $ "☐ " <> prettyFormula phi O
prettyFormula (Exists phi) lvl = surround lvl Z $ "♢ " <> prettyFormula phi O
prettyFormula (Next w phi) lvl = surround lvl Z $ weak w "◯" <> " " <> prettyFormula phi O
prettyFormula (RepeatNext w k phi) lvl = surround lvl Z $ weak w "◯" <> "(" <> show k <> ") " <> prettyFormula phi O
prettyFormula (Until w phi psi) lvl = surround lvl Z $ prettyFormula phi O <> " " <> weak w "U" <> " " <> prettyFormula psi O
prettyFormula (Implies phi psi) lvl = surround lvl Z $ prettyFormula phi O <> " " <> "⇒" <> " " <> prettyFormula psi O
prettyFormula (Or phis) lvl = surround lvl Z $ "(∨)" <> foldl' (<>) "" (fmap (\x -> " " <> prettyFormula x O) phis)
prettyFormula (And phis) lvl = surround lvl Z $ "(∧)" <> foldl' (<>) "" (fmap (\x -> " " <> prettyFormula x O) phis)
prettyFormula (Not phi) lvl = surround lvl Z $ "¬ " <> prettyFormula phi O
prettyFormula Top lvl = surround lvl O "⊤"
prettyFormula Bottom lvl = surround lvl O "⊥"
prettyFormula (PropForall x phi) lvl = surround lvl Z $ "∀" <> x <> ". " <> prettyFormula phi Z
prettyFormula (PropAtom c is) lvl = surround lvl O $ show c <> "(" <> prettyPropConstraints (Set.toList is) <> ")"
prettyFormula (PropEq t v) lvl = surround lvl Z $ prettyPropTerm t <> " = " <> show v
