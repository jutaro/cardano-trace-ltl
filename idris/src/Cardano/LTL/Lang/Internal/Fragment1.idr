module Cardano.LTL.Lang.Internal.Fragment1

import Data.SortedSet as Set

public export
data Frag1 =
    Atom (Set.SortedSet Int)
  | NotAtom (Set.SortedSet Int)
  | And Frag1 Frag1
  | Or Frag1 Frag1
  | Top
  | Bottom

export
notFrag : Frag1 -> Frag1
notFrag (Atom set) = NotAtom set
notFrag (NotAtom set) = Atom set
notFrag (And a b) = Or (notFrag a) (notFrag b)
notFrag (Or a b) = And (notFrag a) (notFrag b)
notFrag Top = Bottom
notFrag Bottom = Top
