{-|
Module      : DPLL
Description : Implementing Davis-Putnam-Logemann-Lovelace algorithm and DPLL algorithm using Haskell functions
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module DPLL where
    
import Data.List

import Common
import CNF
import Text.PrettyPrint

-- | Check if the clause sets is satisfiable, and print out the result.
-- | If it is valid, it yields Ø, which is satisfiable.
-- | If it is invalid, it yields empty clause □, which is unsatisfiable.
--
-- Example:
--
-- > $ dpllResultPrint [[Neg (Var 'r')]]
-- > "It yields Ø, which is satisfiable."
dpllResultPrint :: [[LogicFormula]] -> Doc
dpllResultPrint clauseSet
        | not (null clauseSet) = text "It yields Ø, which is satisfiable."
        | null clauseSet = text "It yields empty clause □, which is unsatisfiable."
        | otherwise = error "DPLL result error"


-- | Apply DPLL algorithm to a CNF formula
-- Check if the formula is not valid, its negation should be satisfiable.
-- DPLL resuiting empty [] which means unsatisfiable, otherwise satisfiable.
--
-- Example:
--
-- > $ dpllFormula (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > [[Neg (Var 'r')]]
dpllFormula :: LogicFormula -> [[LogicFormula]]
dpllFormula formula 
        | length (head clauses) == 1 = unitClause clauses
        | unitClause clauses == unitNegClause clauses = unitClause clauses
        | otherwise = unitClause clauses ++ unitNegClause clauses
        where clauses = toClauses formula

-- | Print out the result of DPLL algorithm to a CNF formula
-- Check if the formula is not valid, its negation should be satisfiable.
-- DPLL resuiting empty [] which means unsatisfiable, otherwise satisfiable.
--
-- Example:
--
-- > $ dpllFormulaPrint (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > ===Applying DPLL algorithm to a CNF formula===
-- > 
-- >  The given formula is: 
-- >  (¬ ((p ∧ q) → (q ∧ r))) 
-- > 
-- >  Convert formula to clause sets... 
-- >     -Step 1: 
-- >      (¬ ((¬ (p ∧ q)) ∨ (q ∧ r))) 
-- > 
-- >     -Step 2: 
-- >      ((p ∧ q) ∧ ((¬ q) ∨ (¬ r))) 
-- > 
-- >  The clause set is: 
-- >  { { p },  { q },  { (¬ q) , (¬ r) } } 
-- > 
-- >  Applying DPLL algorithm to the clause set... 
-- > 
-- >  The answer is: 
-- >  { (¬ r) } 
-- > 
-- >  The result is: 
-- >  It yields Ø, which is satisfiable.
dpllFormulaPrint :: LogicFormula -> Doc
dpllFormulaPrint formula =      text "\n===Applying DPLL algorithm to a CNF formula===\n\n" <+>
                                text "The given formula is: \n" <+>
                                formulaExpre formula <+>
                                text "\n\n Convert formula to clause sets..." <+>
                                text "\n    -Step 1: \n    " <+>
                                formulaExpre afterStep1 <+>
                                text "\n\n    -Step 2: \n    " <+>
                                formulaExpre afterStep2 <+>
                                text "\n\n The clause set is: \n" <+>
                                text "{" <+> clausesPrint (toClauses formula) <+> text "} \n\n" <+>
                                text "Applying DPLL algorithm to the clause set... \n\n" <+>
                                text "The answer is: \n" <+>
                                clausesPrint (dpllFormula formula) <+>
                                text "\n\n The result is: \n" <+>
                                dpllResultPrint (dpllFormula formula)
                        where afterStep1 = step1 formula
                              afterStep2 = step2 afterStep1


-- | Print out the result of DPLL algorithm to clause sets
-- Example:
--
-- > $ dpllClausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
-- > The given formula is:
-- >  (¬ ((p ∧ q) → (q ∧ r)))
-- > 
-- > The clause set is:
-- >  { { p },  { q },  { (¬ q) , (¬ r) } }
dpllClausesPrint :: [[LogicFormula]] -> Doc
dpllClausesPrint clauses =      text "The clause set is: \n" <+>
                                text "{" <+> clausesPrint clauses <+> text "}\n\n" <+>
                                text "Applying DPLL algorithm to the clause set...\n\n" <+>
                                text "The answer is: \n" <+>
                                clausesPrint (dpllClauseSets clauses) <+>
                                text "\n\n The result is: \n" <+>
                                dpllResultPrint (dpllClauseSets clauses)



-- | Main function 2: Apply DPLL algorithm to clause sets
-- DPLL resuiting empty [] means unsatisfiable, otherwise satisfiable
--
-- Example:
--
-- > $ dpllClauseSets (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > [[Neg (Var 'r')]]
dpllClauseSets :: [[LogicFormula]] -> [[LogicFormula]]
dpllClauseSets clauseSet 
        | length (head clauses) == 1 = unitClause clauses
        | unitClause clauses == unitNegClause clauses = unitClause clauses
        | otherwise = unitClause clauses ++ unitNegClause clauses
        where clauses = sortOn length clauseSet


-- | Convert a CNF formula to a clause set
--
-- Example:
--
-- > $ toClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
toClauses :: LogicFormula -> [[LogicFormula]]
toClauses formula = sortOn length (eachClause (toClause (step2 (step1 formula))))       -- ^ sortOn: make the shortest clause in the front


-- | Non-splitting elimination of each clause if exists a unit clause
--
-- Example:
--
-- > $ unitClause [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > [[Neg (Var 'r')]]
-- >
-- > $ unitClause ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitClause :: [[LogicFormula]] -> [[LogicFormula]]
unitClause [] = [[]]
unitClause clauses@(x:xs) 
        | null xs = [x]    -- ^ The case of clause set Ø, just leave [x] as the result for next validation.
        | otherwise = unitClause (sortOn length (eliminate (head x) clauses))

-- | Non-splitting elimination of each clause if exists a unit clause
--
-- Example:
--
-- > $ unitClausePrint [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > [[Neg (Var 'r')]]
-- >
-- > $ unitClausePrint ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitClausePrint :: [[LogicFormula]] -> Doc
unitClausePrint [] = text ""
unitClausePrint clauses@(x:xs)
        | null x =      text "\nSo the answer is { □ }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | null xs =text "\nUse unit" <+> clausesPrint [x] <+> text ": \nSo the answer is { Ø }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | otherwise =   text "\nUse unit" <+> clausesPrint [x] <+> text ": \n" <+>
                        clausesPrint sortedClauses <+>
                        unitClausePrint sortedClauses
                where sortedClauses = sortOn length (eliminate (head x) clauses)


-- | Splitting in case no unit clause exists, the literal should be negated
--
-- Example:
--
-- > $ unitNegClause ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitNegClause :: [[LogicFormula]] -> [[LogicFormula]]
unitNegClause [] = [[]]
unitNegClause clauses@(x:xs) 
        | null xs = [x]    -- ^ The case of clause set Ø
        | otherwise = unitNegClause (sortOn length (eliminate (revNeg (head x)) clauses))


-- | Splitting in case no unit clause exists, the literal should be negated
--
-- Example:
--
-- > $ unitNegClausePrint ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitNegClausePrint :: [[LogicFormula]] -> Doc
unitNegClausePrint [] = text ""
unitNegClausePrint clauses@(x:xs)
        | null x =      text "\nSo the answer is { □ }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | null xs =text "\nUse unit" <+> clausesPrint [x] <+> text ": \nSo the answer is { Ø }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | otherwise =   text "\nUse unit" <+> clausesPrint [x] <+> text ": \n" <+>
                        clausesPrint sortedClauses <+>
                        unitNegClausePrint sortedClauses
                where sortedClauses = sortOn length (eliminate (revNeg (head x)) clauses)


-- | Eliminate all clauses containing specific literal (x),
--  and eliminate all negation of x from all clauses
--
-- Example:
-- 
-- > $ eliminate (Neg (Var 'p')) ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'p',Var 'r']]) []
-- > [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']]
-- > $ eliminate (Var 'r') [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']]
-- > [[Var 'q'],[Neg (Var 'q')]]
-- > $ eliminate (Neg (Var 'q')) [[Var 'q'],[Neg (Var 'q')]]
-- > [[]]
eliminate :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
eliminate _ [] = []
eliminate x (y:ys)
        | x `elem` y = eliminate x ys   -- ^ x: the specific literal, y: the clause
        | revNeg x `elem` y = filter (\z -> z /= x && z /= revNeg x) y : eliminate x ys
        | otherwise = y : eliminate x ys
