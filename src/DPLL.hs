{-# OPTIONS_GHC -fno-warn-unused-imports #-}
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
            , dpllResultSets
            , dpllResultPrint
            , unitClausePrint
            , emptyPrint
            , checkNextSplit
            , dpllElimAll
            , dpllElim
            , toCNFClauses
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
                                text "If the formula is not valid, so its negation should be satisfiable... \n\n" <+>
                                cnfPrint negFormula <+>
                                dpllClausesPrint clauses
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
                                text "{" <+> clausesPrint clauses <+> text "}" <+>
                                unitClausePrint (sortOn length clauses) <+>
                                text "\n\n The result is: \n" <+>
                                dpllResultPrint (dpllResultSets clauses) <+> text "\n"




-- | Check if the clause sets is satisfiable, and print out the result.
-- | If it is valid, it yields Ø, which is satisfiable.
-- | If it is invalid, it yields empty clause □, which is unsatisfiable.
--
-- Example:
--
dpllResultSets :: [[LogicFormula]] -> [BoolValue]
dpllResultSets []  = [F]  -- ^ The answer of □, the case has been eliminated all clauses.
dpllResultSets clauses@(x:xs) 
        | null xs && null nextClauses=  [T]    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | length x > 1 && not (null xs) && checkNextSplit clauses = dpllResultSets negNextClauses ++ dpllResultSets nextClauses
        | otherwise = dpllResultSets nextClauses   -- ^ checkNextSplit clauses: The case do not need to split.                   
                where   start = head x
                        nextClauses = sortOn length (dpllElim start clauses) -- ^ sortOn to make the shortest clause in the front.
                        negNextClauses = sortOn length (dpllElim (revNeg start) clauses)    -- ^ The negation for split case.


-- | Print out the result of DPLL algorithm.
-- | Check if there exists empty clause □, which is unsatisfiable.
dpllResultPrint :: [BoolValue] -> Doc
dpllResultPrint boolValues
        | F `elem` boolValues = text "It exists empty clause □, which is unsatisfiable."    -- ^ If there exists □ in all results, it is unsatisfiable.
        | otherwise = text "It yields Ø, which is satisfiable."    -- ^ All results are Ø, it is satisfiable.



-- | Non-splitting elimination of each clause if exists a unit clause.


-- | Print out the DPLL result of given clauses step by step.
-- | Including the unit literal elimination and split elimination.
--
-- Example:  
--
-- > $ unitClausePrint [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > 
-- >
-- > $ unitClausePrint ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > 
unitClausePrint :: [[LogicFormula]] -> Doc
unitClausePrint [] = text "\n\nSo the answer of this case is { □ }."  -- ^ The answer of □, the case has been eliminated all clauses.
unitClausePrint clauses@(x:xs)
        | null xs && null nextClauses=  text "\n\nSo the answer of this case is { Ø }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | length x > 1 && not (null xs) && checkNextSplit clauses = -- ^ The case of shortest clause have more than 1 literal, so need to split.
                                        text "\n\nIn case of " <+> formulaExpre start <+> text " -> 1: \n" <+>
                                        emptyPrint nextClauses <+> unitClausePrint nextClauses <+> 
                                        text "\n\nIn case of " <+> formulaExpre start <+> text " -> 0: \n" <+>
                                        emptyPrint negNextClauses <+> unitClausePrint negNextClauses
        | otherwise =      text "\n\n" <+> emptyPrint nextClauses <+>  -- ^ checkNextSplit clauses: The case do not need to split.
                                        text "       Use unit " <+> emptyPrint [x] <+> 
                                        unitClausePrint nextClauses
                where   start = head x
                        nextClauses = sortOn length (dpllElim start clauses) -- ^ sortOn to make the shortest clause in the front.
                        negNextClauses = sortOn length (dpllElim (revNeg start) clauses)    -- ^ The negation for split case.


-- | Checks if the clause set is empty and prints out the corresponding result.
-- | This function is used to display the result from @unitClausePrint@. If the next clause is empty, it outputs "{ [] }", indicating that the formula is satisfiable.
emptyPrint :: [[LogicFormula]] -> Doc
emptyPrint clauses
        | null clauses = text "{ [] }"
        | otherwise = clausesPrint clauses


-- | Check if all clause sets have more than 1 literal, if yes, split the specific literal in 2 cases.
checkNextSplit :: [[LogicFormula]] -> Bool
checkNextSplit clauses = dpllElimAll (head (head clauses)) clauses /= clauses -- || dpllElimAll (revNeg (head (head clauses))) clauses /= clauses


-- | Non-splitting elimination of each clause if exists a unit clause.
--
-- Example:
--
-- > $ dpllElimAll (Var 'p') [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > [[Neg (Var 'r')]]
-- >
-- > $ dpllElimAll ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
dpllElimAll :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
dpllElimAll _ [] = [[]]
dpllElimAll start clauses@(x:xs) 
        | null xs = [x]    -- ^ The case of clause set Ø, just leave [x] as the result for next validation.
        | otherwise = dpllElimAll nextStart nextClauses
                where   nextStart = head (head nextClauses)
                        nextClauses = sortOn length (dpllElim start clauses)


-- | Eliminate all clauses containing specific literal (x),
--  and dpllElim all negation of x from all clauses.
--
-- Example:
-- 
-- > $ dpllElim (Neg (Var 'p')) ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'p',Var 'r']]) []
-- > [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']]
-- > $ dpllElim (Var 'r') [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']]
-- > [[Var 'q'],[Neg (Var 'q')]]
-- > $ dpllElim (Neg (Var 'q')) [[Var 'q'],[Neg (Var 'q')]]
-- > [[]]
dpllElim :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
dpllElim _ [] = []
dpllElim x (y:ys)
        | x `elem` y || [revNeg x] == y = dpllElim x ys   -- ^ x: the specific literal, y: the clause
        | revNeg x `elem` y = filter (\z -> z /= x && z /= revNeg x) y : dpllElim x ys
        | otherwise = y : dpllElim x ys


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
