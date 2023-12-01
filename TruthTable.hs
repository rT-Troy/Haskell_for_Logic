module TruthTable where

import Data.List
import Data.Maybe

-- | define the boolvalue type
data BoolValue = T | F deriving (Show, Eq)

-- | Defining data type of basic logic notations
-- ¬ φ, φ ∧ ψ, φ ∨ ψ, φ → ψ, ⊥, ⊤ 
data LogicFormula = Var Char    -- propositional variable
                   | Not LogicFormula
                   | LogicFormula :/\ LogicFormula
                   | LogicFormula :\/ LogicFormula
                   | LogicFormula :-> LogicFormula
                   | Bottom
                   | Top
                       deriving (Show, Eq)


-- | main program
-- TEST:
-- >>> formula1 = ((Var 'p') :\/ (Var 'd'))
-- >>> formula2 = ((Var 'q') :/\(Var 'r'))
-- >>> formulaComb = ((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r'))
-- >>> putStrLn (truthTable formulaComb)
-- >>> putStrLn (truthTable formula1)
-- WAS WAS WAS WAS WAS parse error (possibly incorrect indentation or mismatched brackets)
-- WAS WAS WAS WAS NOW parse error on input `)'
truthTable :: LogicFormula -> String
truthTable formula = firstRow ++ "\n" ++ intercalate "\n" [rowString formula status | status <- allPosStatus (variablesStr formula)]
  where
    firstRow = "0\t" ++ intercalate "\t" (map (\v -> [v]) (variablesStr formula)) ++ "\tResult"
    rowString formula status = intercalate "\t" (map (\v -> showBool (calculator (Var v) status)) (variablesStr formula)) ++ "\t" ++ showBool (calculator formula status)


-- | Get all non-repeating propositional variables from a given formula
-- TEST:
-- >>> variablesStr (Var 'p' :\/ Var 'q')
-- >>> variablesStr (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r')))
-- "pq"
-- "pdqr"
variablesStr :: LogicFormula -> [Char]
variablesStr (Var v) = [v]      -- get propositional variable
variablesStr (Not formula) = variablesStr formula
variablesStr (formula1 :/\ formula2) = nub (variablesStr formula1 ++ variablesStr formula2)
variablesStr (formula1 :\/ formula2) = nub (variablesStr formula1 ++ variablesStr formula2)
variablesStr (formula1 :-> formula2) = nub (variablesStr formula1 ++ variablesStr formula2)
variablesStr Bottom = []
variablesStr Top = []


-- | Generate a nested list of all possible variable assignments
-- TEST:
-- >>> allPosStatus "pd"
allPosStatus :: [Char] -> [[(Char, BoolValue)]]
allPosStatus [] = [[]]
allPosStatus (v:vs) = [(v, T):status | status <- rest] ++ [(v, F):status | status <- rest]
  where rest = allPosStatus vs


-- | calculate the bool value of given formula and case status
-- TEST:
-- >>> calculator (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r'))) [('p',T),('d',T),('q',T),('r',T)]
calculator :: LogicFormula -> [(Char, BoolValue)] -> BoolValue
calculator (Var v) status = fromMaybe (error ("Variable " ++ [v] ++ " not found in environment")) (lookup v status)
calculator (Not formula) status = if calculator formula status == T then F else T

calculator (formula1 :/\ formula2) status = if calculator formula1 status == T && calculator formula2 status == T then T else F
calculator (formula1 :\/ formula2) status = if calculator formula1 status == F && calculator formula2 status == F then F else T
calculator (formula1 :-> formula2) status = if calculator formula1 status == T && calculator formula2 status == F then F else T

calculator Bottom _ = F
calculator Top _ = T


-- | show value of Bool type to String
showBool :: BoolValue -> String
showBool T = "T"
showBool F = "F"
