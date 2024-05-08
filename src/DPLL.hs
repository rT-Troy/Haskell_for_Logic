{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-|
Module      : DPLL
Description : Implementing Davis-Putnam-Logemann-Lovelace (DPLL) algorithm using Haskell functions.
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Implementing Davis-Putnam-Logemann-Lovelace (DPLL) algorithm to a given formula or clause set using Haskell functions.
-}
module DPLL ( dpllFormulaPrint
            , dpllClausesPrint
            , dpllClauses
            , dpllAllPrint
            , dpllResultPrint
            , eachClausePrint
            , dpllResultSatisfy
            , emptyPrint
            , eachClause
            , dpllCheckNextSplit
            , dpllElimAll
            , dpllElim
            , toCNFClauses
            , getPure
            , unitClause
            ) where

import Data.List ( sortOn, nub, find )

import Common
import CNF
import Text.PrettyPrint ( Doc, (<+>), text, vcat )
import Data.Bool (bool)
import Data.Maybe (fromMaybe, listToMaybe)


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

-- | Convert a CNF formula to a clause set.
--
-- Example:
--
-- > $ toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- >
-- > $ toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :<-> (Var 'q' :/\ Var 'r')))
-- > [[Var 'p'],[Var 'r'],[Neg (Var 'r'),Var 'q']]
dpllFormulaPrint :: LogicFormula -> Doc
dpllFormulaPrint formula =      text "\n===Applying DPLL algorithm to a formula===\n\n" <+>
                                text "The given formula is: \n" <+>
                                formulaExpre formula <+>
                                cnfPrint formula <+>
                                dpllClausesPrint clauses
                where
                        clauses = toCNFClauses formula


-- | Print out the result of DPLL algorithm to clause set
-- Example:
--
-- > $ dpllClausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
dpllClausesPrint :: [[LogicFormula]] -> Doc
dpllClausesPrint clauses =      text "\n===Applying DPLL algorithm to a clause set===\n\n" <+>
                                text "The clause set is: \n" <+>
                                text "{" <+> clausesPrint clauses <+> text "}" <+>
                                dpllAllPrint (sortOn length clauses) (fromMaybe [] (unitClause (sortOn length clauses)))  <+>
                                text "\n\n The result is: \n" <+>
                                dpllResultPrint (dpllClauses (sortOn length clauses) (fromMaybe [] (unitClause (sortOn length clauses)))) <+> text "\n"

-- | Check if the clause set is satisfiable, and print out the result set of all possible assignments.
-- | If it is valid, it yields Ø, which is satisfiable.
-- | If it is invalid, it yields empty clause □, which is unsatisfiable.
--
-- Example:
-- > $ dpllClauses [[Var 'p',Var 'q',Neg(Var 'r')],[Neg(Var 'p'),Var 'q',Neg(Var 'r')],[Neg(Var 'q'),Neg(Var 'r')],[Neg(Var 'p'),Var 'r'],[Var 'p',Var 'r']] [Var 'p',Var 'q',Var 'r']
-- > [F,F,F,F,F,F,F,F]
dpllClauses :: [[LogicFormula]] -> [LogicFormula] -> [BoolValue]
dpllClauses _ [] = []
dpllClauses clauses (x:xs) = eachClause clauses x ++ dpllClauses clauses xs


-- | Print out the result of DPLL algorithm.
-- | Check if there exists empty clause □, which is unsatisfiable.
dpllResultPrint :: [BoolValue] -> Doc
dpllResultPrint boolValues
        | boolValues == [] = text "It exists Ø, which is satisfiable."
        | all (== F) boolValues = text "All path yields empty clause □, which is unsatisfiable."
        | otherwise = text "It exists Ø, which is satisfiable."


-- | The satisfiability result is determined by the DPLL.
-- | This function will be used to compare the satisfiability of Truth Table and Resolution in Main.hs.
dpllResultSatisfy :: [BoolValue] -> Bool
dpllResultSatisfy boolValues
        | all (== F) boolValues = False
        | otherwise = True

-- | Print out the result of DPLL algorithm to all possible assignments.
-- | Including the different pure literal elimination.
-- > dpllAllPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']] [Var 'r',Var 'p',Var 'q',Var 's',Var 't']
dpllAllPrint :: [[LogicFormula]] -> [LogicFormula] -> Doc
dpllAllPrint _ [] = text ""
dpllAllPrint clauses (x:xs) = eachClausePrint clauses x <+> dpllAllPrint clauses xs

-- | Print out the DPLL result of given clauses step by step.
-- | Including the unit literal elimination and split elimination.
--
-- Example:  
--
-- > $ eachClausePrint ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']]) (Var 'p')
-- > In case of  p  -> 1: 
-- >  { r },  { q , (¬ r) },  { (¬ q) , (¬ r) } 
-- > 
-- >  { q },  { (¬ q) }        Use unit  { r } 
-- > 
-- >  { [] }        Use unit  { q } 
-- > 
-- > So the answer of this case is { □ }. 
-- > 
-- > In case of  p  -> 0: 
-- >  { r },  { q , (¬ r) },  { (¬ q) , (¬ r) } 
-- > 
-- >  { q },  { (¬ q) }        Use unit  { r } 
-- > 
-- >  { [] }        Use unit  { q } 
-- > 
-- > So the answer of this case is { □ }.
eachClausePrint :: [[LogicFormula]] -> LogicFormula -> Doc
eachClausePrint [] _ = text "\n\nSo the answer of this case is { □ }."    -- ^ The answer of □, the case has been eliminated all clauses.
eachClausePrint clauses@(x:xs) start
        | null xs && null nextClauses=  text "\n\nSo the answer of this case is { Ø }."    -- ^ The case of clause set Ø, but have to print the last clause as unit.
        | length x > 1 && not (null xs) && dpllCheckNextSplit clauses =     -- ^ The case of shortest clause have more than 1 literal, so need to split.
                text "\n\nIn case of {" <+> formulaExpre start <+> text "} -> 1: \n" <+>
                emptyPrint nextClauses <+> vcat (maybe [] (map (eachClausePrint nextClauses . getPure)) (unitClause nextClauses)) <+>
                text "\n\nIn case of {" <+> formulaExpre start <+> text "} -> 0: \n" <+>
                emptyPrint negNextClauses <+> vcat (maybe [] (map (eachClausePrint negNextClauses . getPure)) (unitClause negNextClauses))
        | otherwise =      text "\n\n" <+> emptyPrint nextClauses <+>      -- ^ dpllCheckNextSplit clauses: The case do not need to split.
                text "       Use unit {" <+> formulaExpre start <+> text "}" <+>
                vcat (maybe [] (map (eachClausePrint nextClauses . getPure)) (unitClause negNextClauses))
            where
                    nextClauses = sortOn length (dpllElim start clauses)
                    negNextClauses = sortOn length (dpllElim (revNeg start) clauses)



-- | Generate the result lsit of DPLL algorithm from a given start unit clause.
-- | Including the unit literal elimination and split elimination.
--
-- Example:
--
-- > $ eachClause [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']] (Var 'p')
-- > [F,F]
eachClause :: [[LogicFormula]] -> LogicFormula -> [BoolValue]
eachClause [] _ = [F]
eachClause clauses@(x:xs) start
    | null xs && null nextClauses = [T]
    | length x > 1 && not (null xs) && dpllCheckNextSplit clauses = 
        maybe [] (concatMap (eachClause nextClauses . getPure)) (unitClause nextClauses)
    | otherwise =  maybe [] (concatMap (eachClause nextClauses . getPure)) (unitClause negNextClauses)
    where
        nextClauses = sortOn length (dpllElim start clauses)
        negNextClauses = sortOn length (dpllElim (revNeg start) clauses)


-- | Checks if the clause set is empty and prints out the corresponding result.
-- | This function is used to display the result from @eachClausePrint@. If the next clause is empty, it outputs "{ [] }", indicating that the formula is satisfiable.
emptyPrint :: [[LogicFormula]] -> Doc
emptyPrint clauses
        | null clauses = text "{ [] }"
        | otherwise = clausesPrint clauses


-- | Check if all clause set have more than 1 literal, if yes, split the specific literal in 2 cases.
dpllCheckNextSplit :: [[LogicFormula]] -> Bool
dpllCheckNextSplit clauses = dpllElimAll (getPure (head (head clauses))) clauses /= clauses -- || dpllElimAll (revNeg (head (head clauses))) clauses /= clauses


-- | Non-splitting elimination of each clause if exists a unit clause.
--
-- Example:
--
-- > $ dpllElimAll (Var 'p') [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
-- > [[Neg (Var 'r')]]
-- >
-- > $ dpllElimAll (Var 'p') ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
dpllElimAll :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
dpllElimAll _ [] = [[]]
dpllElimAll start clauses@(x:xs)
        | null xs = [x]    -- ^ The case of clause set Ø, just leave [x] as the result for next validation.
        | otherwise = dpllElimAll nextStart nextClauses
                where   nextStart = getPure (head x)
                        nextClauses = sortOn length (dpllElim start clauses)


getPure :: LogicFormula -> LogicFormula
getPure (Neg x) = x
getPure x = x



-- | Find the unit clause in the clause set or return the first pure literal.
--
-- Example:
--
-- > $ unitClause [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')]]
-- > Just [Var 'p',Var 'q',Var 'r']
unitClause :: [[LogicFormula]] -> Maybe [LogicFormula]
unitClause [[]] = Nothing
unitClause clauses =
    let sortedClauses = sortOn length clauses
    in case listToMaybe sortedClauses of
        Just clause | length clause == 1 -> Just clause
        _ -> Just $ nub (map getPure (concat clauses))


-- | Eliminate all clauses containing specific literal (x),
--  and eliminate all negation of x from all clauses.
--
-- Example:
-- 
-- > $ dpllElim (Neg (Var 'p')) ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'p',Var 'r']])
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


toCNFClauses :: LogicFormula -> [[LogicFormula]]
toCNFClauses formula = sortOn length (cnfAlgo formula)       -- ^ sortOn: make the shortest clause in the front
