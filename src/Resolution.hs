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
module Resolution ( resolution, resoClauses, eachClause, eachLiteral, resolver,
                    validChecker, resoFormulaPrint, resoClausesPrint, resoResultPrint,
                    resoEachPrint, eachLiteralPrint ) where

import Text.PrettyPrint ( Doc, (<+>), text )

import Common
import CNF

resolution :: LogicFormula -> [[LogicFormula]]
resolution formula = eachClause (cnfAlgo formula)


resoFormulaPrint :: LogicFormula -> Doc
resoFormulaPrint formula =  
    text "\n===Apply Resolution to a formula===\n\n" <+>
    text "The given formula is: \n" <+>
    formulaExpre formula <+>
    text "\n\n The negation is: \n" <+>
    formulaExpre negFormula <+>
    text "\n\n If the formula is valid, so its negation should be un-satisfiable... \n" <+>
    text " If the formula is not valid, so its negation should be satisfiable... \n\n" <+>
    cnfPrint negFormula <+>
    resoClausesPrint (resoClauses (cnfAlgo negFormula))
        where   
            negFormula = revNeg formula


resoClausesPrint :: [[LogicFormula]] -> Doc
resoClausesPrint clauses =  text "\n Applying Resolution to the clause set... \n" <+>
                            resoEachPrint clauses <+> resultAnswer 
                        where   
                            resultAnswer = resoResultPrint (resoClauses clauses)


resoResultPrint :: [[LogicFormula]] -> Doc
resoResultPrint clauses =   text "\n\n The result of Resolution is: \n" <+>
                            if validChecker clauses then text "It yields empty clause □, which is unsatisfiable.\n"
                            else text "It yields Ø, which is satisfiable.\n"


resoEachPrint :: [[LogicFormula]] -> Doc
resoEachPrint clauses = text "Resolving the clause yields " <+> clausesPrint clauses <+>
                        eachClausePrint clauses clauses


resoClauses :: [[LogicFormula]] -> [[LogicFormula]]
resoClauses clauses = clauses ++ eachClause clauses


eachClause :: [[LogicFormula]] -> [[LogicFormula]]
eachClause [] = []
eachClause (x:xs) = eachLiteral x xs ++ eachClause (xs ++ eachLiteral x xs)

eachClausePrint :: [[LogicFormula]] -> [[LogicFormula]] -> Doc
eachClausePrint [] _ = text ""
eachClausePrint (x:xs) oriClauses = eachLiteralPrint x xs oriClauses <+> eachClausePrint (xs ++ eachLiteral x xs) oriClauses


eachLiteral :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]]
eachLiteral [] _ = []
eachLiteral (x:xs) clauses = resolver x clauses ++ eachLiteral xs (resolver x clauses)


eachLiteralPrint :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]] -> Doc
eachLiteralPrint [] _ _ = text ""
eachLiteralPrint (x:xs) clauses oriClauses
    | resolver x clauses /= [] = text "\n\nResolving the clause yields " <+>
                                 formulaExpre x <+> text ":\n" <+> 
                                 clausesPrint (oriClauses ++ resolver x clauses) <+> 
                                 eachLiteralPrint xs (resolver x clauses) oriClauses
    | otherwise = text "" <+> eachLiteralPrint xs (resolver x clauses) oriClauses


resolver :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
resolver _ [] = []
resolver literal (x:xs)
    | [revNeg literal] == x = [[]]
    | revNeg literal `elem` x = filter (/= revNeg literal) x : resolver literal xs
    | otherwise = resolver literal xs


validChecker :: [[LogicFormula]] -> Bool
validChecker clauses = [] `elem` clauses