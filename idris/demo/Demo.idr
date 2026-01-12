module Demo

import Cardano.Logging.Types.TraceMessage
import Cardano.LTL.Check
import Cardano.LTL.Lang.Formula
import Cardano.LTL.Pretty
import Cardano.LTL.Satisfy
import Cardano.Trace.Feed
import Data.List
import Data.SortedMap as Map
import Data.SortedSet as Set
import Data.String
import System

record TraceProps where
  constructor TraceProps
  slot : Int

singletonMap : Ord k => k -> v -> Map.SortedMap k v
singletonMap k v = Map.insert k v Map.empty

die : String -> IO a
die msg = do
  putStrLn msg
  exitFailure

isJust : Maybe a -> Bool
isJust (Just _) = True
isJust Nothing = False

findMsg : (TraceMessage -> Bool) -> List TraceMessage -> Maybe TraceMessage
findMsg = find

parseDigits : List Char -> Maybe Int
parseDigits [] = Nothing
parseDigits xs = go xs 0 where
  go : List Char -> Int -> Maybe Int
  go [] acc = Just acc
  go (c :: cs) acc =
    case digitToInt c of
      Nothing => Nothing
      Just n => go cs (acc * 10 + n)

trimLeft : List Char -> List Char
trimLeft [] = []
trimLeft (c :: cs) = if isSpace c then trimLeft cs else c :: cs

extractIntField : String -> String -> Maybe Int
extractIntField key line =
  let pat = unpack ("\"" ++ key ++ "\":") in
  case findSub pat (unpack line) of
    Nothing => Nothing
    Just idx =>
      let rest = dropN (idx + length pat) (unpack line) in
      let rest' = trimLeft rest in
      let (digits, _) = spanList (\c => case digitToInt c of
                                          Just _ => True
                                          Nothing => False) rest'
      in parseDigits digits

implementation Event TemporalEvent String where
  ofTy (msgs, _) c = isJust $ findMsg (\msg => tmsgNS msg == c) msgs
  index (_, idx) = idx
  props (msgs, _) c =
    case findMsg (\msg => tmsgNS msg == c) msgs of
      Just msg =>
        case extractIntField "slot" (tmsgData msg) of
          Just slot => singletonMap (MkPropName "slot") (IntValue slot)
          Nothing => Map.empty
      Nothing => Map.empty

tabulate : Int -> String -> String
tabulate n = intercalate "\n" . map (\line => replicate n ' ' ++ line) . lines

green : String -> String
green text = "\x1b[32m" ++ text ++ "\x1b[0m"

red : String -> String
red text = "\x1b[31m" ++ text ++ "\x1b[0m"

prettyTraceMessage : TraceMessage -> String
prettyTraceMessage msg =
  tmsgNS msg ++
    case extractIntField "slot" (tmsgData msg) of
      Just slot => "(\"slot\" = " ++ show slot ++ ")"
      Nothing => ""

prettyTemporalEvent : TemporalEvent -> String
prettyTemporalEvent (msgs, _) = intercalate "\n" (map prettyTraceMessage msgs)

prettySatisfactionResult : List TemporalEvent -> Formula String -> SatisfactionResult String -> String
prettySatisfactionResult _ initial Satisfied = prettyFormula initial Z ++ " " ++ green "(✔)"
prettySatisfactionResult events initial (Unsatisfied phi rel) =
  prettyFormula initial Z ++ " ⇔ " ++ prettyFormula phi Z ++ " " ++ red "(✗)" ++ "\n" ++
    tabulate 2 (intercalate "\n------\n" (go (Set.toList rel))) where
      go : List Int -> List String
      go [] = []
      go (e :: es) =
        case index e events of
          Just ev => prettyTemporalEvent ev :: go es
          Nothing => go es

intToNat : Int -> Nat
intToNat i = if i <= 0 then Z else S (intToNat (i - 1))

index : Int -> List a -> Maybe a
index i xs = if i < 0 then Nothing else go (intToNat i) xs where
  go : Nat -> List a -> Maybe a
  go Z (x :: _) = Just x
  go (S k) (_ :: rest) = go k rest
  go _ [] = Nothing

check : Formula String -> List TemporalEvent -> IO ()
check phi events = putStrLn (prettySatisfactionResult events phi (satisfies phi events))

prop2 : Formula String
prop2 = PropForall "i" $ Until True
  (Not $
    Or
      [ PropAtom "Forge.Loop.NodeIsLeader" (Set.fromList [PropConstraint (MkPropName "slot") (Var "i")])
      , PropAtom "Forge.Loop.NodeNotLeader" (Set.fromList [PropConstraint (MkPropName "slot") (Var "i")])
      ]
  )
  (PropAtom "Forge.Loop.StartLeadershipCheck" (Set.fromList [PropConstraint (MkPropName "slot") (Var "i")]))

readArgs : List String -> IO (Filename, TemporalEventDurationMicrosec)
readArgs [x, durStr] =
  case parseDigits (unpack durStr) of
    Just dur => pure (x, dur)
    Nothing => die "Usage: <filename> <duration>"
readArgs _ = die "Usage: <filename> <duration>"

main : IO ()
main = do
  args <- getArgs
  (filename, dur) <- readArgs args
  events <- Cardano.Trace.Feed.read filename dur
  check prop2 events
