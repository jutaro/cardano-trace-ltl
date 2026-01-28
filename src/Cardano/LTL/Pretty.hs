{-# LANGUAGE OverloadedStrings #-}

module Cardano.LTL.Pretty (
    Lvl(..)
  , prettyPropValue
  , prettyPropKeyValueList
  , prettyPropTerm
  , prettyPropConstraint
  , prettyPropConstraints
  , prettyFormula) where

import           Cardano.LTL.Lang.Formula
import           Data.List           (foldl')
import qualified Data.Set            as Set
import           Data.Text           (Text, intercalate, pack)
import Data.Maybe (fromMaybe)

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

prettyPropKeyValueList :: [(PropName, PropValue)] -> Text
prettyPropKeyValueList = intercalate "\n" . fmap go where
  go (n, v) = pack (show n) <> " = " <> prettyPropValue v

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

mbSuperscript0to9 :: Int -> Maybe Text
mbSuperscript0to9 0 = Just "⁰"
mbSuperscript0to9 1 = Just "¹"
mbSuperscript0to9 2 = Just "²"
mbSuperscript0to9 3 = Just "³"
mbSuperscript0to9 4 = Just "⁴"
mbSuperscript0to9 5 = Just "⁵"
mbSuperscript0to9 6 = Just "⁶"
mbSuperscript0to9 7 = Just "⁷"
mbSuperscript0to9 8 = Just "⁸"
mbSuperscript0to9 9 = Just "⁹"
mbSuperscript0to9 _ = Nothing

intToSuperscriptH :: Int -> Text
intToSuperscriptH x = fromMaybe "" (mbSuperscript0to9 x)

intToSuperscript :: Int -> Text
intToSuperscript x =
  let d = x `div` 10 in
  let m = x `mod` 10 in
  let x = intToSuperscriptH m in
  if d == 0
  then
    x
  else
    let xs = intToSuperscript d in
    xs <> x


-- | Pretty-print a `Formula` using unicode operators.
prettyFormula :: Show a => Formula a -> Lvl -> Text
prettyFormula (Forall phi) lvl = surround lvl Z $ "☐ ᪲ " <> prettyFormula phi O
prettyFormula (ForallN k phi) lvl = surround lvl Z $ "☐" <> intToSuperscript k <> " " <> prettyFormula phi O
prettyFormula (ExistsN w k phi) lvl = surround lvl Z $ weak w "♢" <> intToSuperscript k <> " " <> prettyFormula phi O
prettyFormula (Next w phi) lvl = surround lvl Z $ weak w "◯" <> " " <> prettyFormula phi O
prettyFormula (NextN w k phi) lvl = surround lvl Z $ weak w "◯" <> intToSuperscript k <> " " <> prettyFormula phi O
prettyFormula (UntilN w k phi psi) lvl = surround lvl Z $
  prettyFormula phi O <> " " <> weak w "|" <> intToSuperscript k <> " " <> prettyFormula psi O
prettyFormula (Implies phi psi) lvl = surround lvl Z $ prettyFormula phi O <> " " <> "⇒" <> " " <> prettyFormula psi O
prettyFormula (Or phis) lvl = surround lvl Z $ "(∨)" <> foldl' (<>) "" (fmap (\x -> " " <> prettyFormula x O) phis)
prettyFormula (And phis) lvl = surround lvl Z $ "(∧)" <> foldl' (<>) "" (fmap (\x -> " " <> prettyFormula x O) phis)
prettyFormula (Not phi) lvl = surround lvl Z $ "¬ " <> prettyFormula phi O
prettyFormula Top lvl = surround lvl O "⊤"
prettyFormula Bottom lvl = surround lvl O "⊥"
prettyFormula (PropForall x phi) lvl = surround lvl Z $ "∀" <> x <> ". " <> prettyFormula phi Z
prettyFormula (PropAtom c is) lvl = surround lvl O $ pack (show c) <> "(" <> prettyPropConstraints (Set.toList is) <> ")"
prettyFormula (PropEq _ t v) lvl = surround lvl Z $ prettyPropTerm t <> " = " <> prettyPropValue v
