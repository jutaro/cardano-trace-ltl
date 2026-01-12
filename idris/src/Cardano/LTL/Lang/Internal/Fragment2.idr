module Cardano.LTL.Lang.Internal.Fragment2

import Data.SortedSet as Set

public export
data Frag2 = Atom (Set.SortedSet Int) | NotAtom (Set.SortedSet Int) | Top | Bottom

export
andFrag : Frag2 -> Frag2 -> Frag2
andFrag (Atom ty) (Atom ty') = Atom (Set.union ty ty')
andFrag (Atom _) (NotAtom _) = Bottom
andFrag (Atom _) Bottom = Bottom
andFrag (Atom ty) Top = Atom ty
andFrag (NotAtom _) (Atom _) = Bottom
andFrag (NotAtom ty) (NotAtom ty') = NotAtom (Set.union ty ty')
andFrag (NotAtom ty) Top = NotAtom ty
andFrag (NotAtom _) Bottom = Bottom
andFrag Top b = b
andFrag Bottom _ = Bottom

export
orFrag : Frag2 -> Frag2 -> Frag2
orFrag (Atom ty) (Atom ty') = Atom (Set.union ty ty')
orFrag (Atom _) (NotAtom _) = Top
orFrag (Atom ty) Bottom = Atom ty
orFrag (Atom _) Top = Top
orFrag (NotAtom _) (Atom _) = Top
orFrag (NotAtom ty) (NotAtom ty') = NotAtom (Set.union ty ty')
orFrag (NotAtom _) Top = Top
orFrag (NotAtom ty) Bottom = NotAtom ty
orFrag Bottom b = b
orFrag Top _ = Top
