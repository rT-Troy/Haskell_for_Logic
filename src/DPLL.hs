{-|
Module      : DPLL
Description : Implementing Davis-Putnam-Logemann-Lovelace (DPLL) algorithm and DPLL algorithm using Haskell functions
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module DPLL ( dpllFormulaPrint
            , dpllClausesPrint
            , dpllFormula
            , dpllClauseSets
            , unitClausePrint
            , unitClause
            , eliminate
            , toCNFClauses
            , dpllResultPrint
            ) where
    
import Data.List ( sortOn, nub )

import Common
import CNF
import Text.PrettyPrint ( Doc, (<+>), text )


-- | Print out the result of DPLL algorithm to a CNF formula.
-- Check if the formula is not valid, its negation should be satisfiable.
-- DPLL resuiting empty [] which means unsatisfiable, otherwise satisfiable.
--
-- Example:
--
-- > $ dpllFormulaPrint ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))
-- > ===Applying DPLL algorithm to a CNF formula===
-- > 
-- >  The given formula is: 
-- >  (¬ ((p ∧ q) → (q ∧ r))) 
-- > 
-- >  The negation is: 
-- >  (¬ ((p ∧ q) → (q ∧ r))) 
-- >
-- > We want to show this formula is not valid, so its negation should be satisfiable...
-- >
-- > ===Apply CNF algorithm to a formula===
-- > 
-- >  The given formula is:
-- >  ((p ∨ q) → (q ∨ r)) 
-- > 
-- > Step 1:
-- >  ((¬ (p ∨ q)) ∨ (q ∨ r)) 
-- > 
-- > Step 2:
-- >  (((¬ p) ∧ (¬ q)) ∨ (q ∨ r)) 
-- > 
-- > Step 3:
-- >  (((¬ p) ∨ (q ∨ r)) ∧ ((¬ q) ∨ (q ∨ r))) 
-- > 
-- > Step 4, the clause set is:
-- >  { { (¬ p) , q , r } }
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
-- >
dpllFormulaPrint :: LogicFormula -> Doc
dpllFormulaPrint formula =      text "\n===Applying DPLL algorithm to a formula===\n\n" <+>
                                text "The given formula is: \n" <+>
                                formulaExpre formula <+>
                                text "\n\n The negation is: \n" <+>
                                formulaExpre negFormula <+>
                                text "\n\n If the formula is valid, so its negation should be un-satisfiable... \n" <+>
                                text " If the formula is not valid, so its negation should be satisfiable... \n\n" <+>
                                cnfPrint negFormula <+>
                                text "\n Applying DPLL algorithm to the clause set... " <+>
                                dpllElimPrint clauses <+>
                                text "\n\nThe result is: \n" <+>
                                dpllResultPrint (dpllFormula negFormula) <+> text "\n"
                where   negFormula = revNeg formula
                        clauses = toCNFClauses negFormula


-- | Print out the result of DPLL algorithm to clause sets
-- Example:
--
-- > $ dpllClausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
-- > ===Applying DPLL algorithm to clause sets===
-- >
-- > The clause set is: 
-- >  { { (¬ r) , (¬ p) , q },  { s , (¬ t) , (¬ p) },  { s , p , r },  { t , s , q },  { (¬ r) , (¬ p) , (¬ q) },  { s , t , r },  { p } }
-- >
-- >  Applying DPLL algorithm to the clause set...
-- > 
-- >  The answer is: 
-- >  { [] } 
-- >
-- >  The result is: 
-- >  It yields Ø, which is satisfiable. 
-- >
dpllClausesPrint :: [[LogicFormula]] -> Doc
dpllClausesPrint clauses =      text "\n===Applying DPLL algorithm to clause sets===\n\n" <+>
                                text "The clause set is: \n" <+>
                                text "{" <+> clausesPrint clauses <+> text "}\n\n" <+>
                                text "Applying DPLL algorithm to the clause set...\n\n" <+>
                                dpllElimPrint clauses <+>
                                text "\n\n The result is: \n" <+>
                                dpllResultPrint (dpllClauseSets clauses) <+> text "\n"


-- | Apply DPLL algorithm to a CNF formula.
-- Check if the formula is not valid, its negation should be satisfiable.
-- DPLL resuiting empty [] which means unsatisfiable, otherwise satisfiable.
--
-- Example:
--
-- > $ dpllFormula (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > [[Neg (Var 'r')]]
dpllFormula :: LogicFormula -> [[LogicFormula]]
dpllFormula formula 
        | length (head clauses) == 1 = unitClause start clauses
        | otherwise = nub (unitClause start clauses ++ unitClause (revNeg start) clauses)
        where   clauses = sortOn length (toCNFClauses formula)
                start = head (head clauses)


dpllElimPrint :: [[LogicFormula]] -> Doc
dpllElimPrint clauses = unitClausePrint start sortedClauses
        where   start = head (head clauses)
                sortedClauses = sortOn length clauses


-- | Main function 2: Apply DPLL algorithm to clause sets.
-- DPLL resuiting empty [] means unsatisfiable, otherwise satisfiable
--
-- Example:
--
-- > $ dpllClauseSets [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
-- > [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p',Var 'r'],[Var 't',Var 's',Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
dpllClauseSets :: [[LogicFormula]] -> [[LogicFormula]]
dpllClauseSets clauseSet 
        | length (head clauses) == 1 = unitClause start clauses
        | otherwise = nub (unitClause start clauses ++ unitClause (revNeg start) clauses)
        where   clauses = sortOn length clauseSet
                start = head (head clauses)


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
        | clauseSet == [[]] = text "It yields empty clause □, which is unsatisfiable."
        | otherwise = text "It yields Ø, which is satisfiable."


-- | Non-splitting elimination of each clause if exists a unit clause.
--
-- Example:
--
-- > $ unitClausePrint (Var 'p') [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > [[Neg (Var 'r')]]
-- >
-- > $ unitClausePrint ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitClausePrint :: LogicFormula -> [[LogicFormula]] -> Doc
unitClausePrint _ [] = text ""
unitClausePrint start clauses@(x:xs)
        | null x =                      text "\n\nSo the answer is { □ }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | null xs =    text "\n\nSo the answer is { Ø }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | length x > 1 && not (null xs) && checkMoreSplit clauses = 
                                        text "\n\nIn case of " <+> formulaExpre start <+> text " -> 1: \n" <+>
                                        clausesPrint nextClauses <+> unitClausePrint nextStart nextClauses <+> 
                                        text "\n\nIn case of " <+> formulaExpre (revNeg start) <+> text " -> 0: \n" <+>
                                        clausesPrint negNextClauses <+> unitClausePrint (revNeg nextStart) nextClauses
        | checkMoreSplit clauses =      text "\n\n" <+> clausesPrint nextClauses <+> 
                                        text "       Use unit " <+> clausesPrint [x] <+>
                                        unitClausePrint nextStart nextClauses
        | otherwise =                   text ""
                where   nextStart = head (head nextClauses)
                        nextClauses =   sortOn length (eliminate start clauses)
                        negNextClauses = sortOn length (eliminate (revNeg start) clauses)


checkMoreSplit :: [[LogicFormula]] -> Bool
checkMoreSplit clauses = (unitClause (head (head clauses)) clauses /= clauses) || (unitClause (revNeg (head (head clauses))) clauses /= clauses)


dpllSplitPrint :: [[LogicFormula]] -> Doc
dpllSplitPrint clauses =text "\nIn case of " <+> formulaExpre start <+> text " -> 1: \n" <+>
                        unitClausePrint start clauses <+> 
                        text "\nIn case of " <+> formulaExpre (revNeg start) <+> text " -> 0: \n" <+>
                        unitClausePrint (revNeg start) clauses
        where   start = head (head clauses)


-- | Non-splitting elimination of each clause if exists a unit clause.
--
-- Example:
--
-- > $ unitClause (Var 'p') [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > [[Neg (Var 'r')]]
-- >
-- > $ unitClause ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitClause :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
unitClause _ [] = [[]]
unitClause start clauses@(x:xs) 
        | null x = []    -- ^ The case of clause set Ø, just leave [x] as the result for next validation.
        | null xs = [x]    -- ^ The case of clause set Ø, just leave [x] as the result for next validation.
        | otherwise = unitClause nextStart nextClauses
                where   nextStart = head (head nextClauses)
                        nextClauses = sortOn length (eliminate start clauses)


-- | Eliminate all clauses containing specific literal (x),
--  and eliminate all negation of x from all clauses.
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
        | x `elem` y || [revNeg x] == y = eliminate x ys   -- ^ x: the specific literal, y: the clause
        | revNeg x `elem` y = filter (\z -> z /= x && z /= revNeg x) y : eliminate x ys
        | otherwise = y : eliminate x ys


-- | Convert a CNF formula to a clause set.
--
-- Example:
--
-- > $ toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- >
-- > $ toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :<-> (Var 'q' :/\ Var 'r')))

toCNFClauses :: LogicFormula -> [[LogicFormula]]
toCNFClauses formula = sortOn length (cnfAlgo formula)       -- ^ sortOn: make the shortest clause in the front
