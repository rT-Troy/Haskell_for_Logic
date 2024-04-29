{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-|
Module      : TruthTable
Description : Construct a truth table for a given formula
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module TruthTable ( truthTablePrint, rowString, tbElimIff, ttSatisfy, truthTableResults, truthTableResultPrint, uniqVars, allPosStatus, calculator, showBool ) where

import Data.List ( intercalate, nub )
import Data.Maybe ( fromMaybe )
import Text.PrettyPrint ( Doc, (<+>), text )

import Common
import CNF


-- | Main function: Generate a pretty truth table of a given formula.
-- Example:
-- 
-- > $ truthTablePrint ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r')))
-- > The given formula is:
-- > ((p → (q → r)) → ((p → q) → (p → r))) 
-- > Truth table result:
-- > p      q       r       Result
-- > T       T       T       T
-- > T       T       F       T
-- > T       F       T       T
-- > T       F       F       T
-- > F       T       T       T
-- > F       T       F       T
-- > F       F       T       T
-- > F       F       F       T
truthTablePrint :: LogicFormula -> Doc
truthTablePrint formula =   text "===Generating Truth Table to a formula===\n\n" <+>
                            text "The non-iff formula is:\n" <+>
                            formulaExpre elimFormula <+>
                            text "\nTruth table result:\n" <+>
                            text (firstRow ++ intercalate "\n" [rowString elimFormula status | status <- allPosStatus (uniqVars (tbElimIff formula))] ) <+>
                            text "\n\n" <+> truthTableResultPrint results <+>
                            text "\n"
                        where
                            elimFormula = tbElimIff formula
                            firstRow = intercalate "\t" (map (: []) (uniqVars elimFormula)) ++ "\tResult\n"
                            results = truthTableResults elimFormula (allPosStatus (uniqVars elimFormula))


tbElimIff :: LogicFormula -> LogicFormula
tbElimIff (f1 :<-> f2) = tbElimIff ((f1 :-> f2) :/\ (f2 :-> f1))
tbElimIff f = f

rowString :: LogicFormula -> [(Char, BoolValue)] -> [Char]
rowString formula status = intercalate "\t" (map (\v -> showBool (calculator (Var v) status)) (uniqVars (tbElimIff formula))) ++
                           "\t" ++ showBool (calculator (tbElimIff formula) status)


truthTableResults :: LogicFormula -> [[(Char, BoolValue)]] -> [BoolValue]
truthTableResults formula status = map (calculator (tbElimIff formula)) status

ttSatisfy :: [BoolValue] -> Bool
ttSatisfy boolValues
    | all (== F) boolValues = False
    | otherwise = True

truthTableResultPrint :: [BoolValue] -> Doc
truthTableResultPrint boolValues
    | all (== T) boolValues = text "All results are true, the formula is valid."
    | all (== F) boolValues = text "All results are false, the formula is unsatisfiable."
    | otherwise = text "Exist true results, the formula is satisfiable."


-- | Get all non-repeating propositional variables from a given formula.
-- Example:
-- 
-- > $ uniqVars ((Var 'p' :\/ Var 'd') :-> (Var 'q' :/\ Var 'r'))
-- > "pdqr"

uniqVars :: LogicFormula -> [Char]
uniqVars (Var v) = [v]      -- get propositional variable
uniqVars (Neg formula) = uniqVars formula
uniqVars (formula1 :/\ formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :\/ formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :-> formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :<-> formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars Bottom = []
uniqVars Top = []


-- | Generate a nested list of all possible variable assignments.
-- Example: 
-- 
-- > $ allPosStatus "pd"
-- > [[('p',T),('d',T)],[('p',T),('d',F)],[('p',F),('d',T)],[('p',F),('d',F)]]

allPosStatus :: [Char] -> [[(Char, BoolValue)]]
allPosStatus [] = [[]]
allPosStatus (x:xs) = [(x, T):status | status <- rest] ++ [(x, F):status | status <- rest]
    where rest = allPosStatus xs


-- | Calculate the bool value of given formula and case status.
-- Example:
-- 
-- > $ calculator (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r'))) [('p',T),('d',T),('q',T),('r',T)]
-- > T
calculator :: LogicFormula -> [(Char, BoolValue)] -> BoolValue
calculator (Var v) status = fromMaybe (error ("Variable '" ++ [v] ++ "' not found in status.")) (lookup v status)
calculator (Neg formula) status = if calculator formula status == T then F else T
calculator (formula1 :/\ formula2) status = if calculator formula1 status == T && calculator formula2 status == T then T else F
calculator (formula1 :\/ formula2) status = if calculator formula1 status == F && calculator formula2 status == F then F else T
calculator (formula1 :-> formula2) status = if calculator formula1 status == T && calculator formula2 status == F then F else T
calculator (_ :<-> _) _ = error "The formula is invalid."
calculator Bottom _ = F
calculator Top _ = T
