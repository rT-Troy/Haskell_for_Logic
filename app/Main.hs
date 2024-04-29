module Main (main, mainClauses) where

import Text.PrettyPrint (Doc, text)

import CNF
import Common
import DPLL
import Resolution
import TruthTable 



-- | Main function: Implementing 

--
-- Example input:
-- > ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r'))
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
    print (formulaSatisfy (ttSatisfy (truthTableResults (tbElimIff formula) (allPosStatus (uniqVars (tbElimIff formula)))))
                          (dpllResultSatisfy (dpllClauses revClauses)) 
                          (prResultSatisfy (prFinalClauses revClauses)))


mainClauses :: IO ()
mainClauses = do
    putStrLn "Please input a clause set:"
    input <- getLine
    let clauses = read input :: [[LogicFormula]]
    print (dpllClausesPrint clauses)
    print (prClausesPrint clauses)
    print (clausesSatisfy (dpllResultSatisfy (dpllClauses clauses)) (prResultSatisfy (prFinalClauses clauses)))

formulaSatisfy :: Bool -> Bool -> Bool -> Doc
formulaSatisfy tt dpll pr
    | tt && dpll && pr = text "All three methods get answer satisfiable."
    | tt && dpll = text "Error: Both Truth Table and DPLL get satisfiable, but Resolution does not."
    | tt && pr = text "Error: Both Truth Table and Resolution get satisfiable, but DPLL does not."
    | dpll && pr = text "Error: Both DPLL and Resolution get satisfiable, but Truth Table does not."
    | tt = text "Error: Truth Table get satisfiable, but DPLL and Resolution do not."
    | dpll = text "Error: DPLL get satisfiable, but Truth Table and Resolution do not."
    | pr = text "Error: Resolution get satisfiable, but Truth Table and DPLL do not."
    | otherwise = text "All three methods get answer unsatisfiable."





clausesSatisfy :: Bool -> Bool -> Doc
clausesSatisfy dpll pr
    | dpll && pr = text "Both DPLL and Resolution get answer satisfiable."
    | dpll = text "Error: DPLL get satisfiable, but Resolution does not."
    | pr = text "Error: Resolution get satisfiable, but DPLL does not."
    | otherwise = text "Both DPLL and Resolution get answer unsatisfiable."
