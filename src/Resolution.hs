{-# OPTIONS_GHC -fno-warn-unused-imports #-}
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
module Resolution  where

import Text.PrettyPrint ( Doc, (<+>), text )

import Common
import CNF
import Data.List (sortOn, nub)

-- | Main function: Implementing propositional resolution in pretty print.


prFormulaPrint :: LogicFormula -> Doc
prFormulaPrint formula =
    text "\n===Apply Resolution to a formula===\n\n" <+>
    text "The given formula is: \n" <+>
    formulaExpre formula <+>
    text "\n\n The negation is: \n" <+>
    formulaExpre negFormula <+>
    text "\n\n If the formula is valid, so its negation should be un-satisfiable... \n" <+>
    text " If the formula is not valid, so its negation should be satisfiable... \n\n" <+>
    cnfPrint negFormula <+>
    prClausesPrint (cnfAlgo negFormula)
        where
            negFormula = revNeg formula



-- | Print the result of propositional resolution, which is either unsatisfiable or satisfiable.
prResultPrint :: [[LogicFormula]] -> Doc
prResultPrint clauses =   text "\n\n The result of Resolution is: \n" <+>
                            if prValidChecker clauses then text "It yields empty clause □, which is unsatisfiable.\n"
                            else text "It yields Ø, which is satisfiable.\n"


-- | Implementing propositional resolution rule to get the final clause set.
-- > $ prClauses [[Var 'p', Var 'q', Var 'r'],[Neg (Var 'p'), Neg (Var 'q')],[Neg (Var 'r')]]
-- [[Var 'p',Var 'q',Var 'r'],[Neg (Var 'p'),Neg (Var 'q')],[Neg (Var 'r')],[Var 'r'],[Var 'p',Var 'q'],[Neg (Var 'p'),Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Neg (Var 'q'),Var 'r'],[]]
-- >
-- > $ prClauses [[Var 'p', Var 'q', Var 'r'],[Var 'p', Neg (Var 'q')],[Neg (Var 'r')]]
-- [[Var 'p',Var 'q',Var 'r'],[Var 'p',Neg (Var 'q')],[Neg (Var 'r')],[Var 'r',Var 'p'],[Var 'p',Var 'q'],[Var 'p',Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'q'),Var 'r',Var 'p'],[Var 'p']]
prClauses :: [[LogicFormula]] -> [[LogicFormula]]
prClauses []  = []
prClauses clauses@(x:xs)
    | prValidChecker clauses = clauses    -- Detected the empty clause, so the clause set is valid.
    | nextNewClauses == xs = clauses    -- The clause set cannot be resolved anymore.
    | otherwise = x : prClauses (nub (xs ++ nextNewClauses))
        where nextNewClauses = prEachClause x xs

-- | Print the final clause set of propositional resolution. 
prClausesPrint :: [[LogicFormula]] -> Doc
prClausesPrint []  = text ""
prClausesPrint clauses@(x:xs)
    | prValidChecker clauses = clausesPrint clauses <+> prResultPrint clauses    -- End the loop, show the resolution clause set.
    | nextNewClauses == xs = clausesPrint clauses <+> text "" <+> prResultPrint clauses    -- The clause set cannot be resolved anymore. 
    | otherwise = clausesPrint [x] <+> prClausesPrint (nub (xs ++ nextNewClauses))
        where nextNewClauses = prEachClause x xs


-- | Apply resolution by specific clause x with all other clauses in the clause set.
-- > $ prEachClause [Var 'p', Var 'q', Neg (Var 'r')] [[Neg (Var 'p'), Neg (Var 'q')],[Var 'r']]
-- > [[Neg (Var 'r')],[Var 'p',Var 'q']]
prEachClause :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]]
prEachClause _ [] = []
prEachClause clause (x:xs) = prResolver clause x : prEachClause clause xs


-- | Implementing propositional resolution rule.
 -- It takes 2 clauses as input, combines them and eliminates the tautological literals in @prElim@.
 --
 -- Example:
 --
 -- > $ prResolver [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r']
 -- > [Var 'p',Var 'q',Neg (Var 's')]
prResolver :: [LogicFormula] -> [LogicFormula] -> [LogicFormula]
prResolver clause1 clause2 = prElim (clause1 ++ clause2)


-- | The elimination of tautological literals in the clause set.
prElim :: [LogicFormula] -> [LogicFormula]
prElim [] = []
prElim (x:xs)
    | x `elem` xs = prElim xs
    | revNeg x `elem` xs = prElim (filter (\y -> y /= x && y /= revNeg x) xs)
    | otherwise = x : prElim xs


-- | Check if the final clause set is valid.
-- | If the empty clause [] is in the clause set, then it is valid.
prValidChecker :: [[LogicFormula]] -> Bool
prValidChecker clauses = [] `elem` clauses