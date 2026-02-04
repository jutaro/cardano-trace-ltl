{-# LANGUAGE OverloadedStrings #-}

module Cardano.LTL.Pretty (
    Prec(..)
  , prettyPropValue
  , prettyPropKeyValueList
  , prettyPropTerm
  , prettyPropConstraint
  , prettyPropConstraints
  , prettyFormula) where

import           Cardano.LTL.Lang.Formula
import           Cardano.LTL.Prec         (Prec)
import qualified Cardano.LTL.Prec         as Prec
import           Data.List                (foldl')
import           Data.Maybe               (fromMaybe)
import qualified Data.Set                 as Set
import           Data.Text                (Text, intercalate, pack)
import qualified Data.Text                as Text

-- | Add parentheses when an inner precedence exceeds the outer one.
surround :: Prec -> Prec -> Text -> Text
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

mbSuperscript0to9 :: Word -> Maybe Text
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

mbSubscript0to9 :: Word -> Maybe Text
mbSubscript0to9 0 = Just "₀"
mbSubscript0to9 1 = Just "₁"
mbSubscript0to9 2 = Just "₂"
mbSubscript0to9 3 = Just "₃"
mbSubscript0to9 4 = Just "₄"
mbSubscript0to9 5 = Just "₅"
mbSubscript0to9 6 = Just "₆"
mbSubscript0to9 7 = Just "₇"
mbSubscript0to9 8 = Just "₈"
mbSubscript0to9 9 = Just "₉"
mbSubscript0to9 _ = Nothing

wordToXscript :: (Word -> Maybe Text) -> Word -> Text
wordToXscript f x =
  let d = x `div` 10 in
  let m = x `mod` 10 in
  let Just x = f m in
  if d == 0
  then
    x
  else
    let xs = wordToXscript f d in
    xs <> x

wordToSuperscript :: Word -> Text
wordToSuperscript = wordToXscript mbSuperscript0to9

wordToSubscript :: Word -> Text
wordToSubscript = wordToXscript mbSubscript0to9


-- | Pretty-print a `Formula` using unicode operators.
prettyFormula :: Show a => Formula a -> Prec -> Text
prettyFormula (Forall k phi) lvl = surround lvl Prec.Prefix $
  "☐ ᪲" <> (if k == 0 then "" else wordToSubscript k) <> " " <> prettyFormula phi Prec.Atom
prettyFormula (ForallN k phi) lvl = surround lvl Prec.Prefix $
  "☐" <> wordToSuperscript k <> " " <> prettyFormula phi Prec.Atom
prettyFormula (ExistsN w k phi) lvl = surround lvl Prec.Prefix $
  weak w "♢" <> wordToSuperscript k <> " " <> prettyFormula phi Prec.Atom
prettyFormula (Next w phi) lvl = surround lvl Prec.Prefix $
  weak w "◯" <> " " <> prettyFormula phi Prec.Atom
prettyFormula (NextN w k phi) lvl = surround lvl Prec.Prefix $
  weak w "◯" <> wordToSuperscript k <> " " <> prettyFormula phi Prec.Atom
prettyFormula (UntilN w k phi psi) lvl = surround lvl Prec.Universe $
  prettyFormula phi Prec.Atom <> " " <> weak w "|" <> wordToSuperscript k <> " " <> prettyFormula psi Prec.Atom
prettyFormula (Implies phi psi) lvl = surround lvl Prec.Implies $
  prettyFormula phi Prec.Or <> " " <> "⇒" <> " " <> prettyFormula psi Prec.Implies
prettyFormula (Or phi psi) lvl = surround lvl Prec.Or $
  prettyFormula phi Prec.Or <> " " <> "∨" <> " " <> prettyFormula psi Prec.And
prettyFormula (And phi psi) lvl = surround lvl Prec.And $
  prettyFormula phi Prec.And <> " " <> "∧" <> " " <> prettyFormula psi Prec.Prefix
prettyFormula (Not phi) lvl = surround lvl Prec.Prefix $
  "¬ " <> prettyFormula phi Prec.Atom
prettyFormula Top lvl = surround lvl Prec.Atom "⊤"
prettyFormula Bottom lvl = surround lvl Prec.Atom "⊥"
prettyFormula (PropForall x phi) lvl = surround lvl Prec.Universe $
  "∀" <> x <> ". " <> prettyFormula phi Prec.Universe
prettyFormula (PropAtom c is) lvl = surround lvl Prec.Atom $
  Text.show c <> "(" <> prettyPropConstraints (Set.toList is) <> ")"
prettyFormula (PropEq _ t v) lvl = surround lvl Prec.Eq $
  prettyPropTerm t <> " = " <> prettyPropValue v
