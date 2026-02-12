{- HLINT ignore "Use <$>" -}
module Cardano.LTL.Lang.Formula.Parser (Parser, text, formula) where


import           Cardano.LTL.Lang.Formula
import           Control.Monad              (guard)
import           Data.Char                  (isAlpha, isAlphaNum)
import           Data.Functor               (void)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as Text
import           Data.Void                  (Void)
import           GHC.Unicode                (isControl)
import           Prelude                    hiding (head)
import           Text.Megaparsec
import           Text.Megaparsec.Char       (char, space, string)
import           Text.Megaparsec.Char.Lexer (decimal, signed)

type Parser = Parsec Void Text

keywords :: [Text]
keywords = []

unescapedVariableIdentifierNextChar :: Parser Char
unescapedVariableIdentifierNextChar = satisfy (\x -> isAlphaNum x || x == '_')

unescapedVariableIdentifier :: Parser Text
unescapedVariableIdentifier =
  Text.pack <$> ((:) <$> firstChar <*> many unescapedVariableIdentifierNextChar) <?> "identifier" where
  firstChar :: Parser Char
  firstChar = satisfy (\x -> isAlpha x || x == '_')

superscriptDigit :: Parser Word
superscriptDigit = 0 <$ char '⁰'
               <|> 1 <$ char '¹'
               <|> 2 <$ char '²'
               <|> 3 <$ char '³'
               <|> 4 <$ char '⁴'
               <|> 5 <$ char '⁵'
               <|> 6 <$ char '⁶'
               <|> 7 <$ char '⁷'
               <|> 8 <$ char '⁸'
               <|> 9 <$ char '⁹'

subscriptDigit :: Parser Word
subscriptDigit = 0 <$ char '₀'
             <|> 1 <$ char '₁'
             <|> 2 <$ char '₂'
             <|> 3 <$ char '₃'
             <|> 4 <$ char '₄'
             <|> 5 <$ char '₅'
             <|> 6 <$ char '₆'
             <|> 7 <$ char '₇'
             <|> 8 <$ char '₈'
             <|> 9 <$ char '₉'

littleEndian :: Word -> [Word] -> Word
littleEndian radix = go 0 1 where
  go :: Word -> Word -> [Word] -> Word
  go acc _ []            = acc
  go acc factor (d : ds) = go (acc + d * factor) (radix * factor) ds

bigEndian :: Word -> [Word] -> Word
bigEndian radix = littleEndian radix . reverse

superscriptWord :: Parser Word
superscriptWord = bigEndian 10 <$> some superscriptDigit

subscriptWord :: Parser Word
subscriptWord = bigEndian 10 <$> some subscriptDigit

int :: Parser Int
int = signed (pure ()) decimal

variableIdentifier :: Parser Text
variableIdentifier = do
  x <- unescapedVariableIdentifier
  guard (x `notElem` keywords)
  pure x

text :: Parser Text
text = Text.pack <$> (char '\"' *> many one) <* char '\"' where
  one :: Parser Char
  one = satisfy (\x -> not (isControl x) && (x /= '"') && (x /= '\n') && (x /= '\r'))

formulaBottom :: Parser (Formula ty)
formulaBottom = Bottom <$ string "⊥"

formulaTop :: Parser (Formula ty)
formulaTop = Top <$ string "⊤"

constraint :: Parser PropConstraint
constraint = PropConstraint <$> (text <* space <* char '=') <*> (space *> propTerm)

constraints :: Parser (Set PropConstraint)
constraints = Set.fromList <$> (char '(' *> space *> sepBy constraint (space *> char ',' <* space) <* space <* char ')')

formulaInParens :: Parser ty -> Parser (Formula ty)
formulaInParens ty = char '(' *> space *> formulaUniverse ty <* space <* char ')'

formulaPropAtom :: Parser ty -> Parser (Formula ty)
formulaPropAtom ty = Atom <$> ty <*> (space *> constraints)

formulaAtom :: Parser ty -> Parser (Formula ty)
formulaAtom ty = formulaBottom <|> formulaTop <|> formulaInParens ty <|> formulaPropAtom ty

formulaNext :: Parser ty -> Parser (Formula ty)
formulaNext ty = Next <$> (string "◯" *> space *> formulaAtom ty)

formulaNextN :: Parser ty -> Parser (Formula ty)
formulaNextN ty = NextN <$> (try (string "◯" *> superscriptWord) <* space) <*> formulaAtom ty

formulaExistsN :: Parser ty -> Parser (Formula ty)
formulaExistsN ty = ExistsN <$> (string "♢" *> superscriptWord <* space) <*> formulaAtom ty

formulaForallN :: Parser ty -> Parser (Formula ty)
formulaForallN ty = ForallN <$> (string "☐" *> superscriptWord <* space) <*> formulaAtom ty

formulaForall :: Parser ty -> Parser (Formula ty)
formulaForall ty = Forall <$> (string "☐ ᪲" *> option 0 subscriptWord <* space) <*> formulaAtom ty

formulaNot :: Parser ty -> Parser (Formula ty)
formulaNot ty = Not <$> (string "¬" *> space *> formulaAtom ty)

propValue :: Parser PropValue
propValue = try (IntValue <$> int) <|> TextValue <$> text

propTerm :: Parser PropTerm
propTerm = try (Const <$> propValue) <|> Var <$> variableIdentifier

formulaEq :: Parser ty -> Parser (Formula ty)
formulaEq ty = try (PropEq Set.empty <$> (propTerm <* space <* char '=') <*> (space *> propValue))
        <|> formulaAtom ty

formulaPrefixOrEq :: Parser ty -> Parser (Formula ty)
formulaPrefixOrEq ty = formulaNextN ty
                   <|> formulaNext ty
                   <|> formulaExistsN ty
                   <|> formulaForall ty
                   <|> formulaForallN ty
                   <|> formulaNot ty
                   <|> formulaEq ty

formulaAnd :: Parser ty -> Parser (Formula ty)
formulaAnd ty = apply <$> (formulaPrefixOrEq ty <* space) <*> optional (do
    void $ string "∧"
    space
    formulaAnd ty) where
  apply :: Formula ty -> Maybe (Formula ty) -> Formula ty
  apply phi Nothing     = phi
  apply phi (Just !psi) = And phi psi

formulaOr :: Parser ty -> Parser (Formula ty)
formulaOr ty = apply <$> (formulaAnd ty <* space) <*> optional (do
    void $ string "∨"
    space
    formulaOr ty) where
  apply :: Formula ty -> Maybe (Formula ty) -> Formula ty
  apply phi Nothing     = phi
  apply phi (Just !psi) = Or phi psi

formulaImplies :: Parser ty -> Parser (Formula ty)
formulaImplies ty = apply <$> (formulaOr ty <* space) <*> optional (do
    void $ string "⇒"
    space
    formulaImplies ty) where
  apply :: Formula ty -> Maybe (Formula ty) -> Formula ty
  apply phi Nothing     = phi
  apply phi (Just !psi) = Implies phi psi

formulaPropForall :: Parser ty -> Parser (Formula ty)
formulaPropForall ty = do
  void $ string "∀"
  space
  x <- variableIdentifier
  space
  void $ string "."
  space
  phi <- formulaUniverse ty
  pure (PropForall x phi)

formulaUntilN :: Parser ty -> Parser (Formula ty)
formulaUntilN ty = apply <$> (formulaImplies ty <* space) <*> optional (do
     void $ string "|"
     k <- superscriptWord
     space
     phi <- formulaImplies ty
     pure (k, phi)) where
  apply :: Formula ty -> Maybe (Word, Formula ty) -> Formula ty
  apply phi Nothing           = phi
  apply phi (Just (!k, !psi)) = UntilN k phi psi

formulaUniverse :: Parser ty -> Parser (Formula ty)
formulaUniverse ty = formulaPropForall ty <|> formulaUntilN ty

formula :: Parser ty -> Parser (Formula ty)
formula = formulaUniverse
