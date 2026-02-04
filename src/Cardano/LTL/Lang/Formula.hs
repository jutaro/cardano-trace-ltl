{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FunctionalDependencies #-}
module Cardano.LTL.Lang.Formula (
    PropName
  , EventIndex
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
import Data.Time.Clock (UTCTime)
import Data.Word (Word64)

-- | A property name (e.g. "thread", "node", etc.).
type PropName = Text

-- | An event index.
type EventIndex = Word

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

-- | Set of indices into relevant events.
type Relevant = Set EventIndex

-- v ::= <int> | "<string>"
-- t ::= <int> | "<string>" | x
-- c ::= "<string>" = t
-- ty ::= <finite type>

-- φ{atom} ::= ⊤ | ⊥ | A p c̄ | (φ{≥universe})
-- φ{eq} ::= t == v
-- φ{prefix} ::= ◯ φ{≥atom} | ◯ᵏ φ{≥atom} | ♢ᵏ φ{≥atom} | ☐ ᪲ₖ φ{≥atom} | ☐ᵏ φ{≥atom} | ¬ φ{≥atom}
-- φ{and} ::= φ{≥and} ∧ φ{>and}
-- φ{or} ::= φ{≥or} ∨ φ{>or}
-- φ{implies} ::= φ{>implies} ⇒ φ{≥implies}
-- φ{universe} ::= ∀x. φ{≥universe} | φ{≥atom} \|ᵏ φ{≥atom}

-- | Default name: φ.
-- | A type of Linear Temporal Logic formulas over a base type ty.
data Formula ty =
   ------------ Temporal -------------
     -- | ☐ ᪲ₖ φ ≡ φ ∧ ◯ (◯ᵏ (☐ ᪲ₖ))
     Forall Word (Formula ty)
     -- | ☐ⁿ φ
     --   ☐⁰ φ ≡ ⊤
     --   ☐¹⁺ᵏ φ ≡ φ ∧ ◯ (☐ᵏ φ)
   | ForallN Word (Formula ty)
     -- | ♢ⁿ φ
     --   ♢⁰ φ ≡ ⊥
     --   ♢¹⁺ᵏ φ ≡ φ ∨ ◯ (♢ᵏ φ)
   | ExistsN Bool Word (Formula ty)
     -- | ◯ φ
   | Next Bool (Formula ty)
     -- | ◯ⁿ φ
     --   ◯⁰ φ ≡ φ
     --   ◯¹⁺ᵏ φ ≡ ◯ (◯ᵏ φ)
   | NextN Bool Word (Formula ty)
     -- | φ |ⁿ ψ
     --   φ |⁰ ψ ≡ ⊤
     --   φ |¹⁺ᵏ ψ ≡ ψ ∨ ¬ ψ ∧ φ ∧ (φ |ᵏ ψ)
   | UntilN Bool Word (Formula ty) (Formula ty)
   -------------------------------------


   ------------ Connective -------------
   | Or (Formula ty) (Formula ty)
     -- | (∧) φ̄, such that
     -- | (∧) [] ≡ ⊤
   | And (Formula ty) (Formula ty)
     -- | ¬ φ
   | Not (Formula ty)
     -- | φ ⇒ ψ
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
  go acc (Forall k phi) = go acc phi
  go acc (ExistsN _ _ phi) = go acc phi
  go acc (Next _ phi) = go acc phi
  go acc (NextN _ _ phi) = go acc phi
  go acc (UntilN _ _ phi psi) = go (go acc phi) psi
  go acc (Or phi psi) = go (go acc phi) psi
  go acc (And phi psi) = go (go acc phi) psi
  go acc (Not phi) = go acc phi
  go acc (Implies phi psi) = go (go acc phi) psi
  go acc Top = acc
  go acc Bottom = acc
  go acc (PropAtom {}) = acc
  go acc (PropForall _ phi) = go acc phi
  go acc (PropEq rel _ _) = rel `union` acc

-- Satisfiability rules of formulas (assuming a background first-order logic):
-- (t̄ ⊧ ∀x. φ) ⇔ (∀x. (t̄ ⊧ φ))
-- (t̄ ⊧ ☐ ᪲ₖ φ) ⇔ (t̄ ⊧ φ ∧ ◯ (◯ᵏ (☐ ᪲ₖ)))
-- (t̄ ⊧ ☐⁰ φ) ⇔ ⊤
-- (t̄ ⊧ ☐¹⁺ᵏ φ) ⇔ (t̄ ⊧ φ ∧ ◯ (☐ᵏ φ))
-- (t̄ ⊧ ♢⁰ φ) ⇔ ⊥
-- (t̄ ⊧ ♢¹⁺ᵏ φ) ⇔ (t̄ ⊧ φ ∨ ◯ (♢ᵏ φ))
-- (_ t̄ ⊧ ◯ φ) ⇔ (t̄ ⊧ φ)
-- (t̄ ⊧ ◯⁰ φ) ⇔ (t̄ ⊧ φ)
-- (t̄ ⊧ ◯¹⁺ᵏ φ) ⇔ (t̄ ⊧ ◯ (◯ᵏ φ))
-- (t̄ ⊧ φ ∨ ψ) ⇔ ((t̄ ⊧ φ) ∨ (t̄ ⊧ ψ))
-- (t̄ ⊧ φ ∧ ψ) ⇔ ((t̄ ⊧ φ) ∧ (t̄ ⊧ ψ))
-- (t̄ ⊧ φ ⇒ ψ) ⇔ ((t̄ ⊧ φ) ⇒ (t̄ ⊧ ψ))
-- (t̄ ⊧ ¬ φ) ⇔ ¬ (t̄ ⊧ φ)
-- (t̄ ⊧ ⊥) ⇔ ⊥
-- (t̄ ⊧ ⊤) ⇔ ⊤
-- (t̄ ⊧ φ |⁰ ψ) ⇔ ⊥
-- (t̄ ⊧ φ |¹⁺ᵏ ψ) ⇔ (t̄ ⊧ ψ ∨ ¬ ψ ∧ φ ∧ (φ |ᵏ ψ))
-- (∅ ⊧ A(p, c̄))   ⇔ ⊥
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
  -- | Is the event of the given type?
  ofTy :: a -> ty -> Bool
  -- | Index of the event.
  index :: a -> EventIndex
  -- | Properties of the event pertinent to the given type.
  --   props e t assumes that ofTy e t = True
  props :: a -> ty -> Map PropVarIdentifier PropValue
  -- | Timestamp of the event (Used for debug & monitoring only, so can be Nothing if not provided).
  beg :: a -> Word64 -- μs since epoch to the beginning of the event
