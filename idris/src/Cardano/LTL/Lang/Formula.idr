module Cardano.LTL.Lang.Formula

import Data.List
import Data.SortedMap as Map
import Data.SortedSet as Set

public export
record PropName where
  constructor MkPropName
  unPropName : String

public export
EventIndex : Type
EventIndex = Int

public export
PropVarIdentifier : Type
PropVarIdentifier = String

public export
Eq PropName where
  (MkPropName x) == (MkPropName y) = x == y

public export
Ord PropName where
  compare (MkPropName x) (MkPropName y) = compare x y

public export
Show PropName where
  show (MkPropName x) = show x

public export
data PropValue =
      IntValue Int
    | TextValue String

public export
data PropTerm = Const PropValue | Var PropVarIdentifier


public export
data PropConstraint = MkPropConstraint PropName PropTerm

public export
Eq PropValue where
  (IntValue x) == (IntValue y) = x == y
  (TextValue x) == (TextValue y) = x == y
  _ == _ = False

public export
Ord PropValue where
  compare (IntValue x) (IntValue y) = compare x y
  compare (IntValue _) (TextValue _) = LT
  compare (TextValue _) (IntValue _) = GT
  compare (TextValue x) (TextValue y) = compare x y

public export
Eq PropTerm where
  (Const x) == (Const y) = x == y
  (Var x) == (Var y) = x == y
  _ == _ = False

public export
Ord PropTerm where
  compare (Const x) (Const y) = compare x y
  compare (Const _) (Var _) = LT
  compare (Var _) (Const _) = GT
  compare (Var x) (Var y) = compare x y

public export
Eq PropConstraint where
  (MkPropConstraint k t) == (MkPropConstraint k' t') = k == k' && t == t'

public export
Ord PropConstraint where
  compare (MkPropConstraint k t) (MkPropConstraint k' t') =
    case compare k k' of
      EQ => compare t t'
      other => other


public export
data Formula ty =
     Forall (Formula ty)
   | Exists (Formula ty)
   | Next Bool (Formula ty)
   | RepeatNext Bool Int (Formula ty)
   | Until Bool (Formula ty) (Formula ty)
   | Or (List (Formula ty))
   | And (List (Formula ty))
   | Not (Formula ty)
   | Implies (Formula ty) (Formula ty)
   | Top
   | Bottom
   | PropAtom ty (Set.SortedSet PropConstraint)
   | PropForall PropVarIdentifier (Formula ty)
   | PropEq (Set.SortedSet EventIndex) PropTerm PropValue

public export
interface Event a ty | a where
  ofTy : a -> ty -> Bool
  index : a -> Int
  props : a -> ty -> Map.SortedMap PropName PropValue

export
relevant : Formula ty -> Set.SortedSet EventIndex
relevant = go Set.empty where
  go : Set.SortedSet EventIndex -> Formula ty -> Set.SortedSet EventIndex
  go acc (Forall phi) = go acc phi
  go acc (Exists phi) = go acc phi
  go acc (Next _ phi) = go acc phi
  go acc (RepeatNext _ _ phi) = go acc phi
  go acc (Until _ phi psi) = go (go acc phi) psi
  go acc (Or phis) = foldl go acc phis
  go acc (And phis) = foldl go acc phis
  go acc (Not phi) = go acc phi
  go acc (Implies phi psi) = go (go acc phi) psi
  go acc Top = acc
  go acc Bottom = acc
  go acc (PropAtom _ _) = acc
  go acc (PropForall _ phi) = go acc phi
  go acc (PropEq rel _ _) = Set.union rel acc
