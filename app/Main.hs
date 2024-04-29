{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main (main) where

import CNF
import Common
import DPLL
import Resolution
import TruthTable 


main :: IO ()
main = do
    putStrLn "Please input a logic formula:"
    input <- getLine
    let formula = strToLogicFormula input
    print (truthTablePrint formula)
    -- Use revNeg to get the negation of the formula,
    -- negFormula will check validity by DPLL and Resolution.
    let negFormula = revNeg formula
    let revClauses = cnfAlgo negFormula
    print (cnfPrint negFormula)
    print (dpllClausesPrint revClauses)
    print (prClausesPrint revClauses)