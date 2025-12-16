{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FunctionalDependencies #-}
module Cardano.LTL.Lang.Formula (
    PropName
  , PropVarIdentifier
  , PropValue(..)
  , PropTerm(..)
  , PropConstraint(..)
  , Formula(..)
  , relevant
  , Event(..)) where

import qualified Data.Map        as Map
import           Data.Map.Strict (Map)
import           Data.Set        (Set, union)
import qualified Data.Set        as Set
import           Data.Text       (Text)

-- | A property name (e.g. "thread", "node", etc.).
type PropName = Text

-- | An event index.
type EventIndex = Int

-- | Default name: x.
-- | Identifier denoting an event property variable.
type PropVarIdentifier = Text

-- | Default name: v.
-- | An event property that can be either `Int` or `Text`.
data PropValue = IntValue Int | TextValue Text deriving (Show, Ord, Eq)

-- | Default name: t.
-- | A term representing a constant property or a variable property.
data PropTerm = Const PropValue | Var PropVarIdentifier deriving (Show, Eq, Ord)

-- | Default name: c.
data PropConstraint = PropConstraint PropName PropTerm deriving (Show, Eq, Ord)

-- v ::= <int> | "<string>"
-- t ::= <int> | "<string>" | x
-- c ::= "<string>" = t
-- ty ::= <finite type>

-- φ{1} ::= ⊤ | ⊥ | A p c̄ | (φ{≥0})
-- φ{0} ::= ☐ φ{≥1} | ∀x. φ{≥0} | t == v | ♢ φ{≥1} | ◯ φ{≥1} | ◯(k) φ{≥1} | φ{≥1} U φ{≥1} | (∨) φ̅̅{̅̅≥̅̅1̅}̅̅ | (∧) φ̅̅{̅̅≥̅̅1̅}̅̅ | ¬ φ{≥1} | φ{≥1} ⇒ φ{≥1}

-- | Default name: φ.
-- | A type of Linear Temporal Logic formulas over a base type ty.
data Formula ty =
   ------------ Temporal -------------
     -- | ☐ φ
     Forall (Formula ty)
     -- | ♢ φ
   | Exists (Formula ty)
     -- | ◯ φ
   | Next Bool (Formula ty)
     -- | ◯(k) φ
   | RepeatNext Bool Int (Formula ty)
     -- | φ | φ
   | Until Bool (Formula ty) (Formula ty)
   -------------------------------------


   ------------ Connective -------------
     -- | ∨ φ̄, such that
     -- | ∨ [] ≡ ⊥
   | Or [Formula ty]
     -- | ∧ φ̄, such that
     -- | ∧ [] ≡ ⊤
   | And [Formula ty]
     -- | ¬ φ
   | Not (Formula ty)
     -- | φ ⇒ φ
   | Implies (Formula ty) (Formula ty)
     -- | T
   | Top
     -- | ⊥
   | Bottom
   -------------------------------------


   ----------- Event property ----------
     -- | A ty c̄
   | PropAtom ty (Set PropConstraint)
     -- | ∀x. φ
   | PropForall PropVarIdentifier (Formula ty)
     -- | i = v
   | PropEq (Set EventIndex) PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------


-- | Compute the set of indices of relevant events.
relevant :: Formula ty -> Set EventIndex
relevant = go mempty where
  go :: Set EventIndex -> Formula ty -> Set EventIndex
  go acc (Forall phi) = go acc phi
  go acc (Exists phi) = go acc phi
  go acc (Next _ phi) = go acc phi
  go acc (RepeatNext _ _ phi) = go acc phi
  go acc (Until _ phi psi) = go (go acc phi) psi
  go acc (Or phis) = foldl' go acc phis
  go acc (And phis) = foldl' go acc phis
  go acc (Not phi) = go acc phi
  go acc (Implies phi psi) = go (go acc phi) psi
  go acc Top = acc
  go acc Bottom = acc
  go acc (PropAtom {}) = acc
  go acc (PropForall _ phi) = go acc phi
  go acc (PropEq rel _ _) = rel `union` acc

-- Satisfiability rules of formulas (assuming a background first-order logic):
-- (t̄ ⊧ ∀x. φ) ⇔ (∀x. (t̄ ⊧ φ))
-- (t t̄ ⊧ ☐ φ) ⇔ ((t t̄ ⊧ φ) ∧ (t̄ ⊧ ☐ φ))
-- (t t̄ ⊧ ♢ φ) ⇔ ((t t̄ ⊧ φ) ∨ (t̄ ⊧ ♢ φ))
-- (_ t̄ ⊧ ◯ φ) ⇔ (t̄ ⊧ φ)
-- (t̄ ⊧ ◯(0) φ) ⇔ (t̄ ⊧ φ)
-- (t t̄ ⊧ ◯(1 + k) φ) ⇔ ((t t̄ ⊧ φ) ∨ (t̄ ⊧ ◯(k) φ))
-- (t̄ ⊧ φ ∨ ψ) ⇔ ((t̄ ⊧ φ) ∨ (t̄ ⊧ ψ))
-- (t̄ ⊧ φ ∧ ψ) ⇔ ((t̄ ⊧ φ) ∧ (t̄ ⊧ ψ))
-- (t̄ ⊧ φ ⇒ ψ) ⇔ ((t̄ ⊧ φ) ⇒ (t̄ ⊧ ψ))
-- (t̄ ⊧ ¬ φ) ⇔ ¬ (t̄ ⊧ φ)
-- (t̄ ⊧ ⊥) ⇔ ⊥
-- (t̄ ⊧ ⊤) ⇔ ⊤
-- (t t̄ ⊧ φ | ψ) ⇔ ((t t̄ ⊧ ψ) ∨ (t t̄ ⊧ φ) ∧ (t̄ ⊧ φ U ψ))
-- (e _ ⊧ A(p, c̄)) ⇔ c̄ ⊆ props e   if ty e = p
--                   ⊥             otherwise
--
-- ∅ ⊆ P ⇔ ⊤
-- {x = t} ⊔ c̄ ⊆ P ⇔ t = P(x) ∧ c̄ ⊆ P   if P(x) is defined
--                   ⊥                  otherwise

-- | A constraint signifying that `a` is an `Event` over base `ty`:
--    — Given an element of `ty`, `ofTy` shall name whether the event is of the given type.
--    — Every event must have a distinct index (witnessed by `index`).
--    — Every event of type `ty` (i.e. `ofTy event = True`) must have a key-value set of properties.
class Event a ty | a -> ty where
  ofTy :: a -> ty -> Bool
  index :: a -> Int
  props :: a -> ty -> Map PropVarIdentifier PropValue
