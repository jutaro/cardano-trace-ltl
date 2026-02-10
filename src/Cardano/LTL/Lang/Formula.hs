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
  , unfoldForall
  , unfoldForallN
  , unfoldExistsN
  , unfoldNextN
  , unfoldUntilN
  , relevance
  , Relevance
  , and
  , interpTimeunit
  , Event(..)) where

import           Data.Map.Strict (Map)
import           Data.Set        (Set, union)
import           Data.Text       (Text)
import           Data.Word       (Word64)
import           Prelude         hiding (and)

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

-- | Set of indices into relevant events together with type of the relevant event.
type Relevance ty = Set (EventIndex, ty)

-- v ::= <int> | "<string>"
-- t ::= <int> | "<string>" | x
-- c ::= "<string>" = t
-- ty ::= <finite type>

-- φ{atom} ::= ⊤ | ⊥ | A ty c̄ | (φ{≥universe})
-- φ{eq} ::= t = v
-- φ{prefix} ::= ◯ φ{≥atom} | ◯ᵏ φ{≥atom} | ♢ᵏ φ{≥atom} | ☐ ᪲ₖ φ{≥atom} | ☐ᵏ φ{≥atom} | ¬ φ{≥atom}
-- φ{and} ::= φ{≥and} ∧ φ{>and}
-- φ{or} ::= φ{≥or} ∨ φ{>or}
-- φ{implies} ::= φ{>implies} ⇒ φ{≥implies}
-- φ{universe} ::= ∀x. φ{≥universe} | φ{≥implies} \|ᵏ φ{≥implies}

-- | Default name: φ.
-- | A type of Linear Temporal Logic formulas over a base type ty.
data Formula ty =
   ------------ Temporal -------------
     -- | ☐ ᪲ₖ φ ≡ φ ∧ ◯ (◯ᵏ (☐ ᪲ₖ))
     --   For every (k+1)-th unit of time from now, φ
     --   For example:
     --     ☐ ᪲₁ φ means for every other unit of time from now, φ
     --     ☐ ᪲₃ φ means for every 4-th unit of time from now, φ
     --     ☐ ᪲₀ φ means for every unit of time from now, φ
     Forall Word (Formula ty)
     -- | ☐ⁿ φ
     --   ☐⁰ φ ≡ ⊤
     --   ☐¹⁺ᵏ φ ≡ φ ∧ ◯ (☐ᵏ φ)
     --   For each of the n units of time from now, φ
   | ForallN Word (Formula ty)
     -- | ♢ⁿ φ
     --   ♢⁰ φ ≡ ⊥
     --   ♢¹⁺ᵏ φ ≡ φ ∨ ◯ (♢ᵏ φ)
     --   For one of the n units of time from now, φ
   | ExistsN Word (Formula ty)
     -- | ◯ φ
     --   For the next unit of time from now, φ.
   | Next (Formula ty)
     -- | ◯ⁿ φ
     --   ◯⁰ φ ≡ φ
     --   ◯¹⁺ᵏ φ ≡ ◯ (◯ᵏ φ)
     --   For the n-th unit of time from now, φ
   | NextN Word (Formula ty)
     -- | φ |ⁿ ψ
     --   φ |⁰ ψ ≡ ⊤
     --   φ |¹⁺ᵏ ψ ≡ ψ ∨ ¬ ψ ∧ φ ∧ (φ |ᵏ ψ)
     --   φ until ψ in the n units of time from now
   | UntilN Word (Formula ty) (Formula ty)
   -------------------------------------


   ------------ Connective -------------
     -- | φ ∨ ψ
   | Or (Formula ty) (Formula ty)
     -- | φ ∧ ψ
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
   | PropEq (Relevance ty) PropTerm PropValue deriving (Show, Eq, Ord)
   -------------------------------------


-- | Compute the total `Relevance` of the formula.
relevance :: Ord ty => Formula ty -> Relevance ty
relevance = go mempty where
  go :: Ord ty => Relevance ty -> Formula ty -> Relevance ty
  go acc (Forall _ phi)     = go acc phi
  go acc (ForallN _ phi)    = go acc phi
  go acc (ExistsN _ phi)    = go acc phi
  go acc (Next phi)         = go acc phi
  go acc (NextN _ phi)      = go acc phi
  go acc (UntilN _ phi psi) = go (go acc phi) psi
  go acc (Or phi psi)       = go (go acc phi) psi
  go acc (And phi psi)      = go (go acc phi) psi
  go acc (Not phi)          = go acc phi
  go acc (Implies phi psi)  = go (go acc phi) psi
  go acc Top                = acc
  go acc Bottom             = acc
  go acc (PropAtom {})      = acc
  go acc (PropForall _ phi) = go acc phi
  go acc (PropEq rel _ _)   = rel `union` acc

unfoldForall :: Word -> Formula ty -> Formula ty
unfoldForall k phi = And phi (Next (NextN k (Forall k phi)))

unfoldForallN :: Word -> Formula ty -> Formula ty
unfoldForallN 0 _   = Top
unfoldForallN k phi = And phi (Next (ForallN (k - 1) phi))

unfoldExistsN :: Word -> Formula ty -> Formula ty
unfoldExistsN 0 _   = Bottom
unfoldExistsN k phi = Or phi (Next (ExistsN (k - 1) phi))

unfoldNextN :: Word -> Formula ty -> Formula ty
unfoldNextN 0 phi = phi
unfoldNextN k phi = Next (NextN (k - 1) phi)

unfoldUntilN :: Word -> Formula ty -> Formula ty -> Formula ty
unfoldUntilN 0 _ _ = Top
unfoldUntilN k phi psi =
  Or psi
     (And
       phi
       (And
         (Not psi)
         (Next (UntilN (k - 1) phi psi))
       )
     )

and :: [Formula ty] -> Formula ty
and []           = Top
and [phi]        = phi
and (phi : phis) = And phi (and phis)

-- | It's useful to express temporal aspect of the formulas in a familiar time unit (e.g milliseconds).
--   Yet, the LTL machinery works with nameless abstract time units.
--   This function can be used to convert one into the other.
interpTimeunit :: (Word -> Word) -> Formula ty -> Formula ty
interpTimeunit f (Forall k phi) = Forall (f k) (interpTimeunit f phi)
interpTimeunit f (ForallN k phi) = ForallN (f k) (interpTimeunit f phi)
interpTimeunit f (ExistsN k phi) = ExistsN (f k) (interpTimeunit f phi)
interpTimeunit f (Next phi) = Next (interpTimeunit f phi)
interpTimeunit f (NextN k phi) = NextN (f k) (interpTimeunit f phi)
interpTimeunit f (UntilN k phi psi) = UntilN (f k) (interpTimeunit f phi) (interpTimeunit f psi)
interpTimeunit f (Not phi) = Not (interpTimeunit f phi)
interpTimeunit f (Or phi psi) = Or (interpTimeunit f phi) (interpTimeunit f psi)
interpTimeunit f (And phi psi) = And (interpTimeunit f phi) (interpTimeunit f psi)
interpTimeunit f (Implies phi psi) = Implies (interpTimeunit f phi) (interpTimeunit f psi)
interpTimeunit _ Top = Top
interpTimeunit _ Bottom = Bottom
interpTimeunit _ phi@PropAtom{} = phi
interpTimeunit _ phi@PropEq{} = phi
interpTimeunit f (PropForall x phi) = PropForall x (interpTimeunit f phi)

-- Satisfiability rules of formulas (assuming a background first-order logic):
-- (∅ ⊧ ◯ (φ ∨ ψ))  ⇔ (∅ ⊧ ◯ φ) ∨ (∅ ⊧ ◯ ψ)
-- (∅ ⊧ ◯ (φ ∧ ψ))  ⇔ (∅ ⊧ ◯ φ) ∧ (∅ ⊧ ◯ ψ)
-- (∅ ⊧ ◯ (φ ⇒ ψ))  ⇔ (∅ ⊧ ◯ φ) ⇒ (∅ ⊧ ◯ ψ)
-- (∅ ⊧ ◯ (¬ φ))    ⇔ ¬ (∅ ⊧ ◯ φ)
-- (∅ ⊧ ◯ ⊥)        ⇔ ⊥
-- (∅ ⊧ ◯ ⊤)        ⇔ ⊤
-- (∅ ⊧ ◯ (t = v))  ⇔ t = v
-- (∅ ⊧ ◯ (A ty c̄)) ⇔ ⊥
-- (∅ ⊧ ◯ (◯ φ)) ⇔ (∅ ⊧ ◯ φ)
-- (∅ ⊧ ◯ (◯ᵏ φ)) ⇔ (∅ ⊧ ◯ φ)
-- (∅ ⊧ ◯ (☐ ᪲ φ)) ⇔ (∅ ⊧ ◯ φ)
-- (∅ ⊧ ◯ (♢⁰ φ)) ⇔ ⊥
-- (∅ ⊧ ◯ (♢¹⁺ᵏ φ)) ⇔ (∅ ⊧ ◯ (φ ∨ ◯ (♢ᵏ φ))) ⇔ ... ⇔ (∅ ⊧ ◯ φ)
-- (∅ ⊧ ◯ (☐⁰ φ)) ⇔ ⊤
-- (∅ ⊧ ◯ (☐¹⁺ᵏ φ)) ⇔ (∅ ⊧ ◯ (φ ∧ ◯ (☐ᵏ φ))) ⇔ ... ⇔ (∅ ⊧ ◯ φ)
-- (∅ ⊧ ◯ (φ |⁰ ψ)) = ⊤
-- (∅ ⊧ ◯ (φ |¹⁺ᵏ ψ)) = (∅ ⊧ ◯ (...))
-- (∅ ⊧ ☐ ᪲ₖ φ) ⇔ (∅ ⊧ φ ∧ ◯ (◯ᵏ (☐ ᪲ φ)))
-- (∅ ⊧ A ty c̄) ⇔ ⊥
--
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
  -- | Timestamp of the event in μs (Used for debug & monitoring only).
  beg :: a -> Word64
