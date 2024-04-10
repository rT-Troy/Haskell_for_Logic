{-|
Module      : CNF
Description : Implementing CNF algorithm and DPLL algorithm using Haskell functions
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module CNF where
import Data.List
import Text.PrettyPrint


import Common

-- | CNF step1: eliminate iff ↔ and implication → from the input formula
-- Example:
--
-- > $ step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
step1 :: LogicFormula -> LogicFormula
step1 (f1 :-> f2) = (step1 (Neg f1)) :\/ (step1 f2)
step1 (f1 :<-> f2) = (step1 (step1 f1 :-> step1 f2)) :/\ (step1 (step1 f2 :-> step1 f1))
step1 (Neg f) = (Neg (step1 f))
step1 (f1 :/\ f2) = (step1 f1 :/\ step1 f2)
step1 (f1 :\/ f2) = (step1 f1 :\/ step1 f2)
step1 Bottom = Bottom
step1 Top = Top
step1 f = f

-- | CNF step2: push negations ¬ towards literals
-- Example:
--
-- > $ step2 (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')
step2 :: LogicFormula -> LogicFormula
step2 (Neg (Neg f)) = step2 f
step2 (Neg (f1 :/\ f2)) = (step2 (Neg f1) :\/ step2 (Neg f2))
step2 (Neg (f1 :\/ f2)) = (step2 (Neg f1) :/\ step2 (Neg f2))
step2 (Neg Bottom) = Top
step2 (Neg Top) = Bottom
step2 (Neg f) = (Neg (step2 f))
step2 (f1 :/\ f2) = (step2 f1 :/\ step2 f2)
step2 (f1 :\/ f2) = (step2 f1 :\/ step2 f2)
step2 (_ :-> _) = error "step1 has bug"
step2 (_ :<-> _) = error "step1 has bug"
step2 f = f


-- | CNF step3: distribute disjunctions ∨ into conjunctions ∧
-- Example:
--
-- > $ step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
step3 :: LogicFormula -> LogicFormula
step3 (x :\/ (y :/\ z)) = (step3 x :\/ step3 y) :/\ (step3 x :\/ step3 z)
step3 ((x :/\ y) :\/ z) = (step3 x :\/ step3 z) :/\ (step3 y :\/ step3 z)
step3 (Neg f) = Neg (step3 f)
step3 (f1 :/\ f2) = (step3 f1) :/\ (step3 f2)
step3 (f1 :\/ f2) = (step3 f1) :\/ (step3 f2)
step3 (_ :-> _) = error "step1 has bug"
step3 (_ :<-> _) = error "step1 has bug"
step3 Bottom = Bottom
step3 Top = Top
step3 f = f

-- | CNF step4: simplify resulting CNF-formulas by eliminating duplicate literals in a clause.
-- Example:
--
-- > $ step4elim ([Neg (Var 'q'),Var 'q',Var 'r'])
-- > [Var 'r']
step4elim :: [LogicFormula] -> [LogicFormula]
step4elim [] = []
step4elim (x:xs)
    | revNeg x `elem` xs = step4elim (filter (\y -> y /= x && y /= revNeg x) xs)
    | otherwise = x : step4elim xs


-- | CNF call function
-- Example:
--
-- > $ cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
cnfAlgo :: LogicFormula -> [[LogicFormula]]
cnfAlgo formula = step4 (step3 (step2 (step1 formula)))


-- | Main function: Implementing CNF algorithm in pretty print
-- Example:
--
-- > $ cnfPrint ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > The given formula is:
-- >  ((p ∨ q) → (q ∨ r)) 
-- > 
-- > The clause set is:
-- >  { { (¬ p) , q , r } }
cnfPrint :: LogicFormula -> Doc
cnfPrint formula  = text "\nApply CNF algorithm to formula" <+>
                    text "The given formula is:\n" <+>
                    formulaExpre formula <+>
                    text "\n\nStep 1:\n" <+>
                    formulaExpre afterStep1 <+>
                    text "\n\nStep 2:\n" <+>
                    formulaExpre afterStep2 <+>
                    text "\n\nStep 3:\n" <+>
                    formulaExpre afterStep3 <+>
                    text "\n\nStep 4, the clause set is:\n" <+>
                    text "{" <+> clausesPrint afterStep4 <+> text "}"
                where afterStep1 = step1 formula
                      afterStep2 = step2 afterStep1
                      afterStep3 = step3 afterStep2
                      afterStep4 = step4 afterStep3


-- | The occurrence of duplicate variables was considered
-- Example:
--
-- > $ step4delsub [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']]
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
step4delsub ::  [[LogicFormula]] -> [[LogicFormula]]
step4delsub [] = []
step4delsub (x:xs)
    | any (\b -> isSubsetOf b x && isSubsetOf x b) xs = error "should not have repeated variable"
    | any (\b -> isSubsetOf x b) xs = step4delsub xs
    | otherwise = x : step4delsub xs
    where isSubsetOf :: [LogicFormula] -> [LogicFormula] -> Bool
          isSubsetOf a b = all (\y -> y `elem` b) a

-- | CNF step4: simplify resulting CNF-formulas by removing duplicate literals
-- Example:
--
-- > $ step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r')))
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
step4 :: LogicFormula -> [[LogicFormula]]
step4 list = step4delsub (reverse (step4delsub (map step4elim (eachClause (toClause list)))))


-- | Convert a CNF formula to a list of clauses
-- Example:
--
-- > $ toClause (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q')))
-- > [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')]
toClause :: LogicFormula -> [LogicFormula]
toClause (clause1 :/\ clause2) = toClause clause1 ++ toClause clause2
toClause clause = [clause]

-- | Convert a list of clauses to a 2D list of literals
-- Example:
--
-- > $ eachClause [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')]
-- > [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'p'),Var 'r'],[Neg (Var 'q')]]
eachClause :: [LogicFormula] -> [[LogicFormula]]
eachClause [] = []
eachClause (clause:clauses) = [eachLiteral clause] ++ eachClause clauses


-- | Convert a clause to a list of literals
-- Example:
--
-- > $ eachLiteral ((Neg (Var 'p') :\/ Var 'q') :\/ Var 'r')
-- > [Neg (Var 'p'),Var 'q',Var 'r']
eachLiteral :: LogicFormula -> [LogicFormula]
eachLiteral (literal1 :\/ literal2) = eachLiteral literal1 ++ eachLiteral literal2
eachLiteral literal = [literal]


-- | Convert a CNF formula to a 2D list of literals (non-repeating)
-- Example:
--
-- > $ toLiteral (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q')))
-- > [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'p'),Var 'r'],[Neg (Var 'q')]]
toLiteral :: LogicFormula -> [[LogicFormula]]
toLiteral formula = nub (eachClause (toClause formula))