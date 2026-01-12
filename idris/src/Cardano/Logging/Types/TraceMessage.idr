module Cardano.Logging.Types.TraceMessage

import Data.List
import Data.String
import Deriving.Show

%language ElabReflection

public export
record TraceMessage where
  constructor MkTraceMessage
  tmsgAt : Int
  tmsgNS : String
  tmsgData : String

%hint
showTraceMessage : Show TraceMessage
showTraceMessage = %runElab derive

isPrefix : Eq a => List a -> List a -> Bool
isPrefix [] _ = True
isPrefix _ [] = False
isPrefix (x :: xs) (y :: ys) = x == y && isPrefix xs ys

findSub : Eq a => List a -> List a -> Maybe Nat
findSub pat [] = Nothing
findSub pat xs@(x :: rest) =
  if isPrefix pat xs then Just Z else map S (findSub pat rest)

dropN : Nat -> List a -> List a
dropN Z xs = xs
dropN (S k) [] = []
dropN (S k) (_ :: xs) = dropN k xs

takeN : Nat -> List a -> List a
takeN Z _ = []
takeN (S k) [] = []
takeN (S k) (x :: xs) = x :: takeN k xs

slice : Nat -> Nat -> List a -> List a
slice start len xs = takeN len (dropN start xs)

spanList : (a -> Bool) -> List a -> (List a, List a)
spanList p [] = ([], [])
spanList p xs@(x :: rest) =
  if p x then
    let (pref, suf) = spanList p rest in
    (x :: pref, suf)
  else
    ([], xs)

trimLeft : List Char -> List Char
trimLeft [] = []
trimLeft (c :: cs) = if isSpace c then trimLeft cs else c :: cs

extractStringField : String -> String -> Maybe String
extractStringField key line =
  let pat = unpack ("\"" ++ key ++ "\":") in
  case findSub pat (unpack line) of
    Nothing => Nothing
    Just idx =>
      let rest = dropN (idx + length pat) (unpack line) in
      let rest' = trimLeft rest in
      case rest' of
        '"' :: chars =>
          let (valChars, _) = spanList (/= '"') chars in
          Just (pack valChars)
        _ => Nothing

collectObject : Nat -> List Char -> Maybe (List Char, List Char)
collectObject depth [] = Nothing
collectObject depth (c :: cs) =
  let depth' = case c of
                 '{' => S depth
                 '}' => case depth of
                          Z => Z
                          S k => k
                 _ => depth
  in if depth' == Z then
       Just ([c], cs)
     else
       case collectObject depth' cs of
         Nothing => Nothing
         Just (obj, rest) => Just (c :: obj, rest)

extractObjectField : String -> String -> Maybe String
extractObjectField key line =
  let pat = unpack ("\"" ++ key ++ "\":") in
  case findSub pat (unpack line) of
    Nothing => Nothing
    Just idx =>
      let rest = dropN (idx + length pat) (unpack line) in
      let rest' = trimLeft rest in
      case rest' of
        '{' :: _ =>
          case collectObject Z rest' of
            Just (obj, _) => Just (pack obj)
            Nothing => Nothing
        _ => Nothing

digitToInt : Char -> Maybe Int
digitToInt '0' = Just 0
digitToInt '1' = Just 1
digitToInt '2' = Just 2
digitToInt '3' = Just 3
digitToInt '4' = Just 4
digitToInt '5' = Just 5
digitToInt '6' = Just 6
digitToInt '7' = Just 7
digitToInt '8' = Just 8
digitToInt '9' = Just 9
digitToInt _ = Nothing

parseDigits : List Char -> Maybe Int
parseDigits [] = Nothing
parseDigits xs = go xs 0 where
  go : List Char -> Int -> Maybe Int
  go [] acc = Just acc
  go (c :: cs) acc =
    case digitToInt c of
      Nothing => Nothing
      Just n => go cs (acc * 10 + n)

isDigitChar : Char -> Bool
isDigitChar c =
  case digitToInt c of
    Just _ => True
    Nothing => False


extractIntField : String -> String -> Maybe Int
extractIntField key line =
  let pat = unpack ("\"" ++ key ++ "\":") in
  case findSub pat (unpack line) of
    Nothing => Nothing
    Just idx =>
      let rest = dropN (idx + length pat) (unpack line) in
      let rest' = trimLeft rest in
      let (digits, _) = spanList isDigitChar rest'
      in parseDigits digits


isAllDigits : List Char -> Bool
isAllDigits [] = False
isAllDigits xs = all isDigitChar xs

isLeap : Int -> Bool
isLeap y = (y `mod` 4 == 0 && y `mod` 100 /= 0) || (y `mod` 400 == 0)

daysInMonth : Int -> Int -> Int
daysInMonth y m =
  case m of
    1 => 31
    2 => if isLeap y then 29 else 28
    3 => 31
    4 => 30
    5 => 31
    6 => 30
    7 => 31
    8 => 31
    9 => 30
    10 => 31
    11 => 30
    12 => 31
    _ => 0

daysBeforeMonth : Int -> Int -> Int
daysBeforeMonth y m = go 1 0 where
  go : Int -> Int -> Int
  go cur acc =
    if cur >= m then acc else go (cur + 1) (acc + daysInMonth y cur)

daysSinceEpoch : Int -> Int -> Int -> Int
daysSinceEpoch y m d =
  let goYear : Int -> Int -> Int
      goYear cur acc =
        if cur >= y then acc else
          goYear (cur + 1) (acc + (if isLeap cur then 366 else 365))
  in goYear 1970 0 + daysBeforeMonth y m + (d - 1)

pow10 : Int -> Int
pow10 n = if n <= 0 then 1 else 10 * pow10 (n - 1)

natToInt : Nat -> Int
natToInt Z = 0
natToInt (S k) = 1 + natToInt k

parseISO8601Micros : String -> Maybe Int
parseISO8601Micros str =
  let chars = unpack str in
  if length chars < 20 then Nothing else
    let yearChars = slice 0 4 chars
        monChars = slice 5 2 chars
        dayChars = slice 8 2 chars
        hourChars = slice 11 2 chars
        minChars = slice 14 2 chars
        secChars = slice 17 2 chars
        restChars = dropN 19 chars
        (microsChars, _) : (List Char, List Char) =
          case restChars of
            '.' :: more => spanList isDigitChar more
            x           => ([], [])
        yearRes = parseDigits yearChars
        monRes = parseDigits monChars
        dayRes = parseDigits dayChars
        hourRes = parseDigits hourChars
        minRes = parseDigits minChars
        secRes = parseDigits secChars
    in do
         y <- yearRes
         mo <- monRes
         d <- dayRes
         h <- hourRes
         mi <- minRes
         s <- secRes
         let microsVal =
               case parseDigits microsChars of
                 Nothing => 0
                 Just us =>
                   let len = length microsChars in
                   us * pow10 (6 - natToInt len)
             totalSecs = daysSinceEpoch y mo d * 86400 + h * 3600 + mi * 60 + s
         pure (totalSecs * 1000000 + microsVal)

parseTimestamp : String -> Maybe Int
parseTimestamp str =
  let chars = unpack str in
  if isAllDigits chars then parseDigits chars else parseISO8601Micros str

-- | Naive decoder for JSON lines containing at/ns/data fields.
-- | Expects an ISO8601 "at" string or a numeric microsecond timestamp.
export
decodeTraceMessage : String -> Either String TraceMessage
decodeTraceMessage line =
  let atString = extractStringField "at" line
      atNumeric = map show (extractIntField "at" line)
      atValue = case atString of
                  Just s => Just s
                  Nothing => atNumeric
      maybeToEither : e -> Maybe a -> Either e a
      maybeToEither err ma =
        case ma of
          Just v => Right v
          Nothing => Left err
  in do
       atStr <- maybeToEither "Missing required fields" atValue
       ns <- maybeToEither "Missing required fields" (extractStringField "ns" line)
       dat <- maybeToEither "Missing required fields" (extractObjectField "data" line)
       at <- maybeToEither "Unable to parse timestamp" (parseTimestamp atStr)
       pure (MkTraceMessage at ns dat)
