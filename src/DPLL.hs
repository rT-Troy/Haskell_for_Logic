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

-- | If T means CNF formula is invalid, if F means valid.
--
-- Example:
--
-- > $ dpllResult (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
-- > T
dpllResult :: LogicFormula -> BoolValue
dpllResult formula
        | lenResult >= 1 = T
        | lenResult == 0 = F 
        | otherwise = error "DPLL result error"
        where lenResult = length (dpllFormula formula)


-- | Main function 1: Apply DPLL algorithm to a CNF formula
-- DPLL resuiting empty [] means unsatisfiable, otherwise satisfiable
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


-- dpllClauseSetsPrint :: [[LogicFormula]] -> Doc


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
        | null xs = [x]
        | otherwise = unitClause (sortOn length (eliminate (head x) clauses))


-- | Splitting in case no unit clause exists, the literal should be negated
--
-- Example:
--
-- > $ unitNegClause ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']])
-- > [[]]
unitNegClause :: [[LogicFormula]] -> [[LogicFormula]]
unitNegClause [] = [[]]
unitNegClause clauses@(x:xs) 
        | null xs = [x]
        | otherwise = unitNegClause (sortOn length (eliminate (revNeg (head x)) clauses))



-- | Check if the clause is valid, if it is, return True, otherwise False
checkClause :: [[LogicFormula]] -> Bool
checkClause result
        | length result == 1 = True      -- ^ ⊤: empty clause set Ø, which means satisfiable
        | otherwise = False              -- ^ ⊥: empty clause □, which means unsatisfiable

-- | Eliminate all clauses containing specific literal (x),
--  and eliminate all negation of x from all clauses
--
-- Example:
-- 
-- > $ eliminate (Neg (Var 'p')) ([[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'p',Var 'r']])
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
