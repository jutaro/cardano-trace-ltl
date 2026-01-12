module Cardano.LTL.Lang.Internal.Fragment0

import Data.List
import Data.SortedSet as Set

public export
data Frag0 =
    Atom (Set.SortedSet Int)
  | Not Frag0
  | And Frag0 Frag0
  | Or Frag0 Frag0
  | Implies Frag0 Frag0
  | Top
  | Bottom

export
andList : List Frag0 -> Frag0
andList = foldl And Top

export
orList : List Frag0 -> Frag0
orList = foldl Or Bottom
