{-# LANGUAGE TypeApplications #-}

module Cardano.LTL.Lang.Formula.Yaml(Exception, readYaml) where

import           Cardano.LTL.Lang.Formula        (Formula)
import           Cardano.LTL.Lang.Formula.Parser (Parser)
import qualified Cardano.LTL.Lang.Formula.Parser as Parser
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Data.Yaml                       (prettyPrintParseException)
import           Data.Yaml.Include               (decodeFileEither)
import           Text.Megaparsec

type YamlExpectedType = [Text]
type Exception = Text

readYaml :: FilePath -> Parser ty -> IO (Either Exception [Formula ty])
readYaml path ty = decodeFileEither @YamlExpectedType path >>= \case
  Left err -> pure (Left (Text.pack $ prettyPrintParseException err))
  Right formulas ->
    case traverse (parse (Parser.formula ty) "input") formulas of
      Left err   -> pure (Left (Text.pack $ errorBundlePretty err))
      Right done -> pure (Right done)
