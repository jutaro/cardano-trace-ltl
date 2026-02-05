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
import           Cardano.LTL.Lang.Prec    (Prec)
import qualified Cardano.LTL.Lang.Prec    as Prec
import qualified Data.Set                 as Set
import           Data.Text                (Text, intercalate, pack)
import qualified Data.Text                as Text

-- | Add parentheses when an inner precedence exceeds the outer one.
surround :: Prec -> Prec -> Text -> Text
surround outer inner str | outer <= inner = str
surround _ _ str = "(" <> str <> ")"

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

superscript0to9 :: Word -> Text
superscript0to9 0 = "⁰"
superscript0to9 1 = "¹"
superscript0to9 2 = "²"
superscript0to9 3 = "³"
superscript0to9 4 = "⁴"
superscript0to9 5 = "⁵"
superscript0to9 6 = "⁶"
superscript0to9 7 = "⁷"
superscript0to9 8 = "⁸"
superscript0to9 9 = "⁹"
superscript0to9 _ = undefined

subscript0to9 :: Word -> Text
subscript0to9 0 = "₀"
subscript0to9 1 = "₁"
subscript0to9 2 = "₂"
subscript0to9 3 = "₃"
subscript0to9 4 = "₄"
subscript0to9 5 = "₅"
subscript0to9 6 = "₆"
subscript0to9 7 = "₇"
subscript0to9 8 = "₈"
subscript0to9 9 = "₉"
subscript0to9 _ = undefined

wordToXscript :: (Word -> Text) -> Word -> Text
wordToXscript f x =
  let d = x `div` 10 in
  let m = x `mod` 10 in
  let ch = f m in
  if d == 0
  then
    ch
  else
    let xs = wordToXscript f d in
    xs <> ch

wordToSuperscript :: Word -> Text
wordToSuperscript = wordToXscript superscript0to9

wordToSubscript :: Word -> Text
wordToSubscript = wordToXscript subscript0to9


-- | Pretty-print a `Formula` using unicode operators.
prettyFormula :: Show a => Formula a -> Prec -> Text
prettyFormula (Forall k phi) lvl = surround lvl Prec.Prefix $
  "☐ ᪲" <> (if k == 0 then "" else wordToSubscript k) <> " " <> prettyFormula phi Prec.Atom
prettyFormula (ForallN k phi) lvl = surround lvl Prec.Prefix $
  "☐" <> wordToSuperscript k <> " " <> prettyFormula phi Prec.Atom
prettyFormula (ExistsN k phi) lvl = surround lvl Prec.Prefix $
  "♢" <> wordToSuperscript k <> " " <> prettyFormula phi Prec.Atom
prettyFormula (Next phi) lvl = surround lvl Prec.Prefix $
  "◯" <> " " <> prettyFormula phi Prec.Atom
prettyFormula (NextN k phi) lvl = surround lvl Prec.Prefix $
  "◯" <> wordToSuperscript k <> " " <> prettyFormula phi Prec.Atom
prettyFormula (UntilN k phi psi) lvl = surround lvl Prec.Universe $
  prettyFormula phi Prec.Atom <> " " <> "|" <> wordToSuperscript k <> " " <> prettyFormula psi Prec.Atom
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
