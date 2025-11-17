{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cardano.LTL.Lang (LTL(..), Result(..), satisfies) where

-- φ
data LTL a =
     -- | ☐ φ
     Forall (LTL a)
     -- | ♢ φ
   | Exists (LTL a)
     -- | ◯ φ
   | Next {weak :: Bool, phi :: LTL a}
     -- | ◯(k) φ
   | RepeatNext {weak :: Bool, idx :: Int, phi :: LTL a}
     -- | φ U φ
   | Until {weak :: Bool, phi :: LTL a, psi :: LTL a}
     -- | ∨ φ̄, such that
     -- | ∨ [] ≡ ⊥
   | Or [LTL a]
     -- | ∧ φ̄, such that
     -- | ∧ [] ≡ ⊤
   | And [LTL a]
     -- | ¬ φ
   | Not (LTL a)
     -- | φ ⇒ φ
   | Implies (LTL a) (LTL a)
     -- | ⊥
   | Top
     -- | T
   | Bottom
     -- | A
   | Atom {pred :: a -> Bool}

-- Equivalence of formulas (w.r.t. satisfiability):
-- (☐ φ)(t :: t̄) <=> φ(t :: t̄) ∧ (☐ φ)(t̄)
-- (♢ φ)(t :: t̄) <=> φ(t :: t̄) ∨ (♢ φ)(t̄)
-- (◯ φ)(_ :: t̄) <=> φ(t̄)
-- (◯(0) φ)(t̄) <=> φ(t̄)
-- (◯(1 + k) φ)(_ :: t̄) <=> (◯(k) φ)(t̄)
-- (φ ∨ ψ)(t̄) <=> φ(t̄) ∨ ψ(t̄)
-- (φ ∧ ψ)(t̄) <=> φ(t̄) ∧ ψ(t̄)
-- (φ ⇒ ψ)(t̄) <=> φ(t̄) ⇒ ψ(t̄)
-- (¬ φ)(t̄) <=> ¬ (φ (t̄))
-- ⊥(_) <=> ⊥
-- ⊤(_) <=> ⊤
-- (φ U ψ)(t :: t̄) = ψ(t :: t̄) ∨ φ(t :: t̄) ∧ (φ U ψ)(t̄)
-- Aₚ(t :: _) <=> p(t)

data Relevance a = Relevant Bool a

instance Functor Relevance where
  fmap f (Relevant t x) = Relevant t (f x)

instance Applicative Relevance where
  pure = Relevant False
  Relevant b f <*> Relevant b' x = Relevant (b || b') (f x)

irrelevant :: a -> Relevance a
irrelevant = Relevant False

relevant :: a -> Relevance a
relevant = Relevant True

-- | Fast forwards the formula through the given event.
-- | Returns an equivalent formula and whether the event is "relevant".
-- | An event is relevant in a formula iff the formula contains an atom whose predicate evalutes to true at the event "now".
step :: LTL a -> a -> Relevance (LTL a)
step (Forall phi) s = (\x -> And [x, Forall phi]) <$> step phi s
step (Exists phi) s = (\x -> Or [x, Exists phi]) <$> step phi s
step (Next _ phi) _ = irrelevant phi
step (RepeatNext _ 0 phi) s = step phi s
step (RepeatNext w k phi) _ = irrelevant $ RepeatNext w (k - 1) phi
step (And phis) s = And <$> traverse (`step` s) phis
step (Or phis) s = Or <$> traverse (`step` s) phis
step (Implies phi psi) s = Implies <$> step phi s <*> step psi s
step (Not phi) s = Not <$> step phi s
step Bottom _ = irrelevant Bottom
step Top _ = irrelevant Top
step (Atom p) s = if p s then relevant Top else irrelevant Bottom
step (Until w phi psi) s = (\x y -> Or [x, And [y, Until w phi psi]]) <$> step psi s <*> step phi s

-- | Check if the formula is a tautology, assuming the end of timeline.
end :: LTL a -> Bool
end (Forall _) = True
end (Exists _) = False
end (Next w _) = w
end (RepeatNext _ 0 phi) = end phi
end (RepeatNext w _ _) = w
end (And phis) = foldl' (&&) True (fmap end phis)
end (Or phis) = foldl' (||) False (fmap end phis)
end (Implies phi psi) = not (end phi) || end psi
end (Not phi) = not (end phi)
end (Until w _ _) = w
end Bottom = False
end Top = True
end (Atom _) = False

-- | The result of checking satisfaction of a formula against a timeline.
-- | If unsatisfied, stores points in the timeline "relevant" to the formula.
data Result a = Satisfied | Unsatisfied [a]

-- | Check if the formula is satisfied in the given timeline.
satisfies :: Foldable f => LTL a -> f a -> Result a
satisfies formula = toResult . foldl' apply ([], formula) where
  apply :: ([a], LTL a) -> a -> ([a], LTL a)
  apply (acc, formula) x =
    let !(Relevant !r !formula') = step formula x in
    (if r then x : acc else acc, formula')

  toResult :: ([a], LTL a) -> Result a
  toResult (acc, formula) = if end formula then Satisfied else Unsatisfied (reverse acc)
