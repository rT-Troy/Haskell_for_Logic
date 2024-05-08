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
    rmFirst,
    prValidChecker
) where

import Text.PrettyPrint ( Doc, (<+>), text )

import Common
import CNF
import Data.List (sortOn, nub)

-- | Main function: Implement Propositional Resolution for a logic formula in pretty print.
-- | It will first apply CNF algorithm to the formula, then apply Resolution to the clause set.
prFormulaPrint :: LogicFormula -> Doc
prFormulaPrint formula =
    text "\n===Apply Resolution to a formula===\n\n" <+>
    text "The given formula is: \n" <+>
    formulaExpre formula <+>
    cnfPrint formula <+>
    prClausesPrint (cnfAlgo formula)



-- | Main function: Implement Propositional Resolution for a clause set in pretty print.
-- 
-- Example:
-- > $ prClausesPrint [[Var 'p',Var 'q'],[Var 'p',Neg(Var 'q')],[Neg(Var 'p'),Var 'q'],[Neg(Var 'p'),Neg(Var 'q')]]
-- > ===Applying Resolution to a clause set=== 
-- > 
-- >  The resolution clause set is: 
-- >  { p , q } { p , (¬ q) } { (¬ p) , q } { (¬ p) , (¬ q) } { p } { q },  { q , (¬ q) },  { p , (¬ p) },  { (¬ q) , q },  { p , (¬ p) },  { (¬ q) },  { p },  { p , (¬ q) },  { (¬ q) , p },  { (¬ p) },  { q },  { (¬ p) , q },  { q , (¬ p) },  { q , (¬ q) },  { (¬ p) , p },  { (¬ q) },  { (¬ p) },  { (¬ p) , (¬ q) },  { (¬ q) , (¬ p) },  { p },  { [] },  { q },  { (¬ q) } 
-- > 
-- >  It yields empty clause □, which is unsatisfiable.
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
    | prValidChecker clauses = clauses    -- Detected the empty clause, so the clause set is unsatisfiable.
    | allElem nextNewClauses xs = clauses    -- The clause set cannot be resolved anymore.
    | otherwise = x : prFinalClauses (xs ++ nextNewClauses)
        where nextNewClauses = nub (prEachClause x xs)

allElem :: [[LogicFormula]] -> [[LogicFormula]] -> Bool
allElem [] _ = True
allElem (x:xs) ys = x `elem` ys && allElem xs ys

-- | Check if the final clause set is unsatisfiable.
-- | If the empty clause [] is in the clause set, then it is unsatisfiable.
prValidChecker :: [[LogicFormula]] -> Bool
prValidChecker clauses = [] `elem` clauses

-- | Print the final clause set of propositional resolution. 
prFinalClausesPrint :: [[LogicFormula]] -> Doc
prFinalClausesPrint []  = text ""
prFinalClausesPrint clauses@(x:xs)
    | prValidChecker clauses = clausesPrint clauses    -- End the loop, show the resolution clause set.
    | allElem nextNewClauses xs = clausesPrint clauses    -- The clause set cannot be resolved anymore. 
    | otherwise = clausesPrint [x] <+> prFinalClausesPrint (xs ++ nextNewClauses)
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
 -- > $ prResolver [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r']
 -- > [Var 'p',Var 'q',Neg (Var 's')]
 -- > $ prResolver [Var 'p',Neg (Var 'r')] [Neg (Var 'p'),Var 'r']
prResolver :: [LogicFormula] -> [LogicFormula] -> [[LogicFormula]]
prResolver clause1 clause2 = nub (prElim (clause1 ++ clause2) (clause1 ++ clause2))
-- | The elimination of tautological literals in the clause set.
-- 
-- Example:
-- > $ prElim [Var 'p',Neg (Var 'r'),Neg (Var 'p'),Var 'r'] [Var 'p',Neg (Var 'r'),Neg (Var 'p'),Var 'r']
-- > [[Neg (Var 'r'),Var 'r'],[Var 'p',Neg (Var 'p')]]
prElim :: [LogicFormula] -> [LogicFormula] -> [[LogicFormula]]
prElim [] _ = []
prElim (x:xs) oriClauses
    | revNeg x `elem` xs = nub (rmFirst (revNeg x) (rmFirst x oriClauses)) : prElim xs oriClauses
    | otherwise = prElim xs oriClauses
-- | Remove the first occurrence of a specific literal in a list.
--
-- Example:
-- > $ rmFirst (Var 'p') [Var 'p',Var 'p',Var 'p',Neg (Var 'r'),Neg (Var 'p'),Var 'r']
-- > [Var 'p',Var 'p',Neg (Var 'r'),Neg (Var 'p'),Var 'r']
rmFirst :: LogicFormula -> [LogicFormula] -> [LogicFormula]
rmFirst _ [] = []
rmFirst x (y:ys)
    | x == y = ys
    | otherwise = y : rmFirst x ys


