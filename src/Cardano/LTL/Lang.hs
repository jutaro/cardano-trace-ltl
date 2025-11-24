{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FunctionalDependencies #-}
module Cardano.LTL.Lang (
    PropName
  , PropVarIdentifier
  , PropValue(..)
  , PropTerm(..)
  , PropConstraint(..)
  , Formula(..)
  , Event(..)) where

import           Data.Map.Strict (Map)
import           Data.Set        (Set)

-- | A property name (e.g. "thread", "node", etc.).
type PropName = String

-- | Default name: x.
-- | Identifier denoting an event property variable.
type PropVarIdentifier = String

-- | Default name: v.
-- | An event property that can be either `Int` or `String`.
data PropValue = IntValue Int | StringValue String deriving (Show, Ord, Eq)

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
   ------------ Temproral -------------
     -- | ☐ φ
     Forall (Formula ty)
     -- | ♢ φ
   | Exists (Formula ty)
     -- | ◯ φ
   | Next Bool (Formula ty)
     -- | ◯(k) φ
   | RepeatNext Bool Int (Formula ty)
     -- | φ U φ
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
   | PropEq PropTerm PropValue deriving Show
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
-- (t t̄ ⊧ φ U ψ) ⇔ ((t t̄ ⊧ ψ) ∨ (t t̄ ⊧ φ) ∧ (t̄ ⊧ φ U ψ))
-- (e _ ⊧ A(p, c̄)) ⇔ c̄ ⊆ props e   if ty e = p
--                   ⊥             otherwise
--
-- ∅ ⊆ P ⇔ ⊤
-- {x = t} ⊔ c̄ ⊆ P ⇔ t = P(x) ∧ c̄ ⊆ P   if P(x) is defined
--                   ⊥                  otherwise

-- | A type `a` is a (temporal) `Event` if:
-- |  — it has a type `ty` (shall be isomorphic to a finite set)
-- |  — it has a set of key-value pairs `props` of integer or string properties
class Event a ty | a -> ty where
  ty :: a -> ty
  props :: a -> Map String PropValue
