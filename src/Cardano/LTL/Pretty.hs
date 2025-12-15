{-# LANGUAGE OverloadedStrings #-}

module Cardano.LTL.Pretty (
    Lvl(..)
  , prettyPropValue
  , prettyPropTerm
  , prettyPropConstraint
  , prettyPropConstraints
  , prettyFormula) where

import           Cardano.LTL.Lang.Formula
import           Data.List           (foldl')
import qualified Data.Set            as Set
import           Data.Text           (Text, intercalate, pack)

data Lvl = Z | O deriving (Show, Eq, Ord)

-- | Add parentheses when an inner precedence exceeds the outer one.
surround :: Lvl -> Lvl -> Text -> Text
surround outer inner str | outer <= inner = str
surround _ _ str = "(" <> str <> ")"

-- | Mark a connective as weak when requested.
weak :: Bool -> Text -> Text
weak True x  = x <> "˜"
weak False x = x

-- | Render a property value.
prettyPropValue :: PropValue -> Text
prettyPropValue (IntValue i)  = pack (show i)
prettyPropValue (TextValue x) = x

-- | Render a property term.
prettyPropTerm :: PropTerm -> Text
prettyPropTerm (Var x)     = x
prettyPropTerm (Const idx) = prettyPropValue idx

-- | Render a single property constraint.
prettyPropConstraint :: PropConstraint -> Text
prettyPropConstraint (PropConstraint k v) = pack (show k) <> " = " <> prettyPropTerm v

-- | Render a list of property constraints.
prettyPropConstraints :: [PropConstraint] -> Text
prettyPropConstraints = intercalate ", " . fmap prettyPropConstraint

-- | Pretty-print a `Formula` using unicode operators.
prettyFormula :: Show a => Formula a -> Lvl -> Text
prettyFormula (Forall phi) lvl = surround lvl Z $ "☐ " <> prettyFormula phi O
prettyFormula (Exists phi) lvl = surround lvl Z $ "♢ " <> prettyFormula phi O
prettyFormula (Next w phi) lvl = surround lvl Z $ weak w "◯" <> " " <> prettyFormula phi O
prettyFormula (RepeatNext w k phi) lvl = surround lvl Z $ weak w "◯" <> "(" <> pack (show k) <> ") " <> prettyFormula phi O
prettyFormula (Until w phi psi) lvl = surround lvl Z $ prettyFormula phi O <> " " <> weak w "|" <> " " <> prettyFormula psi O
prettyFormula (Implies phi psi) lvl = surround lvl Z $ prettyFormula phi O <> " " <> "⇒" <> " " <> prettyFormula psi O
prettyFormula (Or phis) lvl = surround lvl Z $ "(∨)" <> foldl' (<>) "" (fmap (\x -> " " <> prettyFormula x O) phis)
prettyFormula (And phis) lvl = surround lvl Z $ "(∧)" <> foldl' (<>) "" (fmap (\x -> " " <> prettyFormula x O) phis)
prettyFormula (Not phi) lvl = surround lvl Z $ "¬ " <> prettyFormula phi O
prettyFormula Top lvl = surround lvl O "⊤"
prettyFormula Bottom lvl = surround lvl O "⊥"
prettyFormula (PropForall x phi) lvl = surround lvl Z $ "∀" <> x <> ". " <> prettyFormula phi Z
prettyFormula (PropAtom c is) lvl = surround lvl O $ pack (show c) <> "(" <> prettyPropConstraints (Set.toList is) <> ")"
prettyFormula (PropEq t v) lvl = surround lvl Z $ prettyPropTerm t <> " = " <> prettyPropValue v
