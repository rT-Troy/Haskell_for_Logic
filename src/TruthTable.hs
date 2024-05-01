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
--
-- Example:
-- 
-- > $ truthTablePrint ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r')))
-- > ===Generating Truth Table to a formula===
-- >
-- >  The non-iff formula is:
-- >  ((p → (q → r)) → ((p → q) → (p → r))) 
-- > Truth table result:
-- >  p      q       r       Result
-- > T       T       T       T
-- > T       T       F       T
-- > T       F       T       T
-- > T       F       F       T
-- > F       T       T       T
-- > F       T       F       T
-- > F       F       T       T
-- > F       F       F       T
-- >  All results are true, the formula is valid. 
truthTablePrint :: LogicFormula -> Doc
truthTablePrint formula =   text "===Generating Truth Table to a formula===\n\n" <+>
                            text "The non-iff formula is:\n" <+>
                            formulaExpre elimFormula <+>
                            text "\nTruth table result:\n" <+>
                            text (firstRow ++ intercalate "\n" [rowString elimFormula status | status <- allPosStatus (uniqVars elimFormula)] ) <+>
                            text "\n\n" <+> truthTableResultPrint results <+>
                            text "\n"
                        where
                            elimFormula = tbElimIff formula
                            firstRow = intercalate "\t" (map (: []) (uniqVars elimFormula)) ++ "\tResult\n"
                            results = truthTableResults elimFormula (allPosStatus (uniqVars elimFormula))


-- | Eliminate iff in a given formula, the new formula will be used to generate truth table.
tbElimIff :: LogicFormula -> LogicFormula
tbElimIff (f1 :<-> f2) = tbElimIff ((f1 :-> f2) :/\ (f2 :-> f1))
tbElimIff (Neg (f1 :<-> f2)) = Neg (tbElimIff ((f1 :-> f2) :/\ (f2 :-> f1)))
tbElimIff (Var v) = Var v
tbElimIff (Neg formula) = Neg (tbElimIff formula)
tbElimIff (f1 :/\ f2) = tbElimIff f1 :/\ tbElimIff f2
tbElimIff (f1 :\/ f2) = tbElimIff f1 :\/ tbElimIff f2
tbElimIff (f1 :-> f2) = tbElimIff f1 :-> tbElimIff f2
tbElimIff Bottom = Bottom
tbElimIff Top = Top


-- | Show the T/F of truth talbe in a more readable way.
rowString :: LogicFormula -> [(Char, BoolValue)] -> [Char]
rowString formula status = intercalate "\t" (map (\v -> showBool (calculator (Var v) status)) (uniqVars (tbElimIff formula))) ++
                           "\t" ++ showBool (calculator (tbElimIff formula) status)


-- | Collection of all result set of possible assignments.
truthTableResults :: LogicFormula -> [[(Char, BoolValue)]] -> [BoolValue]
truthTableResults formula status = map (calculator (tbElimIff formula)) status


-- | The satisfiability result of a formula is determined by the truth table.
-- | This function will be used to compare the satisfiability of DPLL and Resolution in Main.hs.
ttSatisfy :: [BoolValue] -> Bool
ttSatisfy boolValues
    | all (== F) boolValues = False
    | otherwise = True


-- | Print the result according to satisfiability.
truthTableResultPrint :: [BoolValue] -> Doc
truthTableResultPrint boolValues
    | all (== T) boolValues = text "All results are true, the formula is valid."
    | all (== F) boolValues = text "All results are false, the formula is unsatisfiable."
    | otherwise = text "Exist true results, the formula is satisfiable."


-- | Get all non-repeating propositional variables from a given formula.
-- | The variables will be used to generate all possible variable assignments.
-- Example:
-- 
-- > $ uniqVars ((Var 'p' :\/ Var 'd') :-> (Var 'q' :/\ Var 'r'))
-- > "pdqr"
uniqVars :: LogicFormula -> [Char]
uniqVars (Var v) = [v]      -- get propositional variable
uniqVars (Neg formula) = uniqVars formula
uniqVars (f1 :/\ f2) = nub (uniqVars f1 ++ uniqVars f2)
uniqVars (f1 :\/ f2) = nub (uniqVars f1 ++ uniqVars f2)
uniqVars (f1 :-> f2) = nub (uniqVars f1 ++ uniqVars f2)
uniqVars (f1 :<-> f2) = nub (uniqVars f1 ++ uniqVars f2)
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


-- | Calculate the True or False of given formula and variable assignments.
-- Example:
-- 
-- > $ calculator (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r'))) [('p',T),('d',T),('q',T),('r',T)]
-- > T
calculator :: LogicFormula -> [(Char, BoolValue)] -> BoolValue
calculator (Var v) status = fromMaybe (error ("Variable '" ++ [v] ++ "' not found in status.")) (lookup v status)
calculator (Neg formula) status = if calculator formula status == T then F else T
calculator (f1 :/\ f2) status = if calculator f1 status == T && calculator f2 status == T then T else F
calculator (f1 :\/ f2) status = if calculator f1 status == F && calculator f2 status == F then F else T
calculator (f1 :-> f2) status = if calculator f1 status == T && calculator f2 status == F then F else T
calculator (_ :<-> _) _ = error "Error: The formula should not contain '<->'."
calculator Bottom _ = F
calculator Top _ = T
