{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-missing-export-lists #-}

{-|
Module      : Resolution
Description : Implementing Propositional Resolution using Haskell functions.
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Implementing Propositional Resolution to a given formula or clause set using Haskell functions.
-}
module Resolution (
    prFormulaPrint,
    prClausesPrint,
    prResultPrint,
    prResultSatisfy,
    prFinalClauses,
    prFinalClausesPrint,
    prEachClause,
    prResolver,
    prElim,
    prValidChecker
) where

import Text.PrettyPrint ( Doc, (<+>), text )

import Common
import CNF
import Data.List (sortOn, nub)

-- | Main function: Implement Propositional Resolution for a logic formula in pretty print.
prFormulaPrint :: LogicFormula -> Doc
prFormulaPrint formula =
    text "\n===Apply Resolution to a formula===\n\n" <+>
    text "The given formula is: \n" <+>
    formulaExpre formula <+>
    text "\n\n If the formula is valid, so its negation should be un-satisfiable... \n" <+>
    text " If the formula is not valid, so its negation should be satisfiable... \n\n" <+>
    cnfPrint formula <+>
    prClausesPrint (cnfAlgo formula)



-- | Main function: Implement Propositional Resolution for a clause set in pretty print.
prClausesPrint :: [[LogicFormula]] -> Doc
prClausesPrint clauses =    text "\n===Applying Resolution to a clause set===" <+>
                            text "\n\n The resolution clause set is: \n" <+>
                            prFinalClausesPrint clauses <+> text "\n\n" <+>
                            prResultPrint (prResultSatisfy clauses)


-- | Print the result of propositional resolution, which is either unsatisfiable or satisfiable.
prResultPrint :: Bool -> Doc
prResultPrint satis = if satis then text "It yields Ø, which is satisfiable.\n"
                        else text "It yields empty clause □, which is unsatisfiable.\n"


-- | The satisfiability result of a clauses is determined by Propositional Resolution.
-- | This function will be used to compare the satisfiability of Truth Table and Resolution in Main.hs.
prResultSatisfy :: [[LogicFormula]] -> Bool
prResultSatisfy clauses
    | prValidChecker finalClauses = False
    | otherwise = True
        where finalClauses = prFinalClauses clauses


-- | Implementing propositional resolution rule to get the final clause set.
-- > $ prFinalClauses [[Var 'p', Var 'q', Var 'r'],[Neg (Var 'p'), Neg (Var 'q')],[Neg (Var 'r')]]
-- [[Var 'p',Var 'q',Var 'r'],[Neg (Var 'p'),Neg (Var 'q')],[Neg (Var 'r')],[Var 'r'],[Var 'p',Var 'q'],[Neg (Var 'p'),Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Neg (Var 'q'),Var 'r'],[]]
-- >
-- > $ prFinalClauses [[Var 'p', Var 'q', Var 'r'],[Var 'p', Neg (Var 'q')],[Neg (Var 'r')]]
-- [[Var 'p',Var 'q',Var 'r'],[Var 'p',Neg (Var 'q')],[Neg (Var 'r')],[Var 'r',Var 'p'],[Var 'p',Var 'q'],[Var 'p',Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'q'),Var 'r',Var 'p'],[Var 'p']]
prFinalClauses :: [[LogicFormula]] -> [[LogicFormula]]
prFinalClauses []  = []
prFinalClauses clauses@(x:xs)
    | prValidChecker clauses = clauses    -- Detected the empty clause, so the clause set is valid.
    | nextNewClauses == xs = clauses    -- The clause set cannot be resolved anymore.
    | otherwise = x : prFinalClauses (nub (nextNewClauses))
        where nextNewClauses = nub (prEachClause x xs)

-- | Print the final clause set of propositional resolution. 
prFinalClausesPrint :: [[LogicFormula]] -> Doc
prFinalClausesPrint []  = text ""
prFinalClausesPrint clauses@(x:xs)
    | prValidChecker clauses = clausesPrint clauses    -- End the loop, show the resolution clause set.
    | nextNewClauses == xs = clausesPrint clauses    -- The clause set cannot be resolved anymore. 
    | otherwise = clausesPrint [x] <+> prFinalClausesPrint (nub (xs ++ nextNewClauses))
        where nextNewClauses = nub (prEachClause x xs)


-- | Apply resolution by specific clause x with all other clauses in the clause set.
-- > $ prEachClause [Var 'p', Var 'q', Neg (Var 'r')] [[Neg (Var 'p'), Neg (Var 'q')],[Var 'r']]
-- > [[Neg (Var 'r')],[Var 'p',Var 'q']]
prEachClause :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]]
prEachClause _ [] = []
prEachClause clause (x:xs) = prResolver clause x ++ prEachClause clause xs


-- | Implementing propositional resolution rule.
 -- It takes 2 clauses as input, combines them and eliminates the tautological literals in @prElim@.
 --
 -- Example:
 --
 -- > $ prResolver [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r', (Neg (Var 'q'))]
 -- > [Var 'p',Var 'q',Neg (Var 's')]
prResolver :: [LogicFormula] -> [LogicFormula] -> [[LogicFormula]]
prResolver clause1 clause2 = nub (prElim (clause1 ++ clause2) (clause1 ++ clause2))


-- | The elimination of tautological literals in the clause set.
prElim :: [LogicFormula] -> [LogicFormula] -> [[LogicFormula]]
prElim [] _ = []
prElim (x:xs) oriClauses
    | revNeg x `elem` xs = rmFirst (revNeg x) (rmFirst x oriClauses) : prElim xs oriClauses
    | otherwise = prElim xs oriClauses


rmFirst :: LogicFormula -> [LogicFormula] -> [LogicFormula]
rmFirst _ [] = []
rmFirst x (y:ys)
    | x == y = ys
    | otherwise = y : rmFirst x ys


-- | Check if the final clause set is valid.
-- | If the empty clause [] is in the clause set, then it is valid.
prValidChecker :: [[LogicFormula]] -> Bool
prValidChecker clauses = [] `elem` clauses