module Cardano.LTL.Satisfy

import Cardano.LTL.Lang.Formula
import Cardano.LTL.Lang.Internal.GuardedFormula as G
import Cardano.LTL.Lang.Internal.HomogeneousFormula as H
import Cardano.LTL.Pretty
import Cardano.LTL.Transform
import Data.SortedSet as Set

public export
data SatisfactionResult ty = Satisfied | Unsatisfied (Formula ty) (Set.SortedSet Int) 

traceFormula : Show ty => String -> Formula ty -> Formula ty
traceFormula _ x = x

traceGuardedFormula : Show ty => String -> G.GuardedFormula ty -> G.GuardedFormula ty
traceGuardedFormula _ x = x

satisfies : (Event event ty, Ord ty, Show ty, Eq (Formula ty)) 
  => Formula ty 
  -> List event 
  -> SatisfactionResult ty
satisfies formula xs = toResult $ foldl apply (0, formula) xs where
  apply : (Event event ty, Eq ty) => Pair Int (Formula ty) -> event -> Pair Int (Formula ty)
  apply (n, formula0) m =
    let formula1 = traceFormula "initial:" formula0
        formula2 = traceGuardedFormula "stepped:" (step formula1 m)
        formula3 = traceGuardedFormula "simplified-next:" (simplifyNext formula2)
        formula4 = traceGuardedFormula "simplified-frag:" (simplifyFragment formula3)
        formula5 = traceFormula "forwarded:" (G.forward formula4)
        formula6 = traceFormula "simplified:" (simplify formula5)
    in (n + 1, formula6)

  toResult : Eq ty => Pair Int (Formula ty) -> SatisfactionResult ty
  toResult (_, formula') =
    let final = traceFormula "end:" 
                    (simplify (G.toFormula (simplifyFragment 
                        (H.toGuardedFormula (terminate formula')))))
    in if final == Top then Satisfied else Unsatisfied final (relevant final)
