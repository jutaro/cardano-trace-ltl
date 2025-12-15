{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FunctionalDependencies #-}
module Cardano.LTL.Lang.Formula (
    PropName
  , PropVarIdentifier
  , PropValue(..)
  , PropTerm(..)
  , PropConstraint(..)
  , Formula(..)
  , Finite(..)
  , Event(..)) where

import qualified Data.Map        as Map
import           Data.Map.Strict (Map)
import           Data.Set        (Set, union)
import qualified Data.Set        as Set
import           Data.Text       (Text)

-- | A property name (e.g. "thread", "node", etc.).
type PropName = Text

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
-- | The base type is assumed to be a finite set (up to isomorphism).
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
   | PropEq PropTerm PropValue deriving (Show, Eq, Ord)
   -- i = 0 ⇒ i = 0 ∧ i = 0
   -------------------------------------

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

-- | `ty` is a finite set.
class Finite ty where
  -- | All elements of the set.
  elements :: Set ty

-- | A type `a` is a (temporal) `Event` of a finite type `ty` if:
-- |  — It specifies which types are included in the event (ty -> Bool or 𝒫(ty)).
-- |  — For every `ty` included in the event it has a set of key-value pairs `props` of integer or string properties for that `ty`.
class Finite ty => Event a ty | ty -> a where
  -- | Check whether the event is of the given type.
  ty :: a -> ty -> Bool
  -- | Assuming the event is of the given type, get all properties of that type.
  props :: a -> ty -> Map Text PropValue
