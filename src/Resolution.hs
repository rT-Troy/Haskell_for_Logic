{-|
Module      : Resolution
Description : Propositional Resolution
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module Resolution ( resolution, resoClauses, eachClause, eachLiteral, resolver, validChecker) where

import Text.PrettyPrint ( Doc, (<+>), text )
import Debug.Trace ( trace, traceShow )

import Common
import CNF

resolution :: LogicFormula -> [[LogicFormula]]
resolution formula = eachClause (cnfAlgo formula)


resoClauses :: [[LogicFormula]] -> [[LogicFormula]]
resoClauses  clauses = clauses ++ eachClause clauses


eachClause :: [[LogicFormula]] -> [[LogicFormula]]
eachClause [] = []
eachClause (x:xs) = eachLiteral x xs ++ eachClause (xs ++ eachLiteral x xs)

eachLiteral :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]]
eachLiteral [] _ = []
eachLiteral (x:xs) clauses = resolver x clauses ++ eachLiteral xs (resolver x clauses)

resolver :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
resolver _ [] = []
resolver literal clauses@(x:xs)
    | [revNeg literal] == x = [[]]
    | revNeg literal `elem` x = filter (/= revNeg literal) x : resolver literal xs
    | otherwise = resolver literal xs

validChecker :: [[LogicFormula]] -> Bool
validChecker clauses = [] `elem` clauses

-- -- | Implementing propositional resolution to a formula.
-- --
-- -- Example:
-- --
-- -- > $ resolClauses [[Var 'p',Var 'q'],[Var 'p',Neg (Var 'q')],[Neg (Var 'p'),Var 'q'],[Neg (Var 'p'),Neg (Var 'q')]]
-- -- > [Var 'p',Var 'q',Neg (Var 's')]
-- resoFormulaPrint :: LogicFormula -> Doc
-- resoFormulaPrint formula =  text "\n===Apply Resolution to a formula===\n\n" <+>
--                             text "The given formula is: \n" <+>
--                             formulaExpre formula <+>
--                             text "\n\n The negation is: \n" <+>
--                             formulaExpre negFormula <+>
--                             text "\n\n If the formula is valid, so its negation should be un-satisfiable... \n" <+>
--                             text " If the formula is not valid, so its negation should be satisfiable... \n\n" <+>
--                             cnfPrint negFormula <+>
--                             text "\n Applying Resolution to the clause set... "

--                         where negFormula = revNeg formula

-- -- > $ resoClausesPrint [[Var 'p',Var 'q'],[Var 'p',Neg (Var 'q')],[Neg (Var 'p'),Var 'q'],[Neg (Var 'p'),Neg (Var 'q')]]
-- -- > [Var 'p',Var 'q',Neg (Var 's')]
-- resoClausesPrint :: [[LogicFormula]] -> Doc
-- resoClausesPrint clauses =  text "\n===Apply Resolution to clause sets===\n\n" <+>
--                             text "The clause set is: \n" <+>
--                             text "{" <+> clausesPrint clauses <+> text "}\n\n" <+>
--                             text "Applying Resolution to the clause set... " <+>








-- -- resoStepsPrint :: [[LogicFormula]] -> Doc
-- -- resoStepsPrint clauses = 


-- -- | Approach 1: Implementing propositional resolution rule to clause sets.
-- -- It takes 2 clauses as input, combines them and eliminates the tautological literals in @resoElim@.
-- --
-- -- Example:
-- --
-- -- > $ concatenates [[Neg (Var 'p')],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r']]
-- -- > []
-- concatenates :: [[LogicFormula]] -> [LogicFormula]
-- concatenates clauses = resoElim (concat clauses)


-- -- | Approach 1: Eliminating the tautological literals in a combined literal list of 2 clauses.
-- --
-- -- Example:
-- --
-- -- > $ resoElim [Var 'p', Var 'q', Neg (Var 'r'), Neg (Var 's'), Var 'r']
-- -- > [Var 'p',Var 'q',Neg (Var 's')]
-- resoElim :: [LogicFormula] -> [LogicFormula]
-- resoElim [] = []
-- resoElim (x:xs)
--     | revNeg x `elem` xs || x `elem` xs = resoElim (rmFirst (revNeg x) xs)
--     | otherwise = x : resoElim xs


-- -- | Approach 1: Removing the first occurrence of a literal in a list of literals.
-- rmFirst :: LogicFormula -> [LogicFormula] -> [LogicFormula]
-- rmFirst _ [] = []
-- rmFirst literal (l:ls)
--     | literal == l = ls
--     | otherwise = l : rmFirst literal ls