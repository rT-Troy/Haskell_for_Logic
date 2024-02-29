{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- | Task 1 - construct truth tables for given formulas
module TruthTable where

import Data.List
import Data.Maybe
import Text.PrettyPrint

import Common


-- | Generate a pretty truth table of a given formula
-- truthTable ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r')))
truthTable :: LogicFormula -> Doc
truthTable formula = text "The given formula is:\n" <+>
                     formulaExpre formula <+>
                     text "\nTruth table result:\n" <+>
                     text (firstRow ++ intercalate "\n" [rowString status | status <- allPosStatus (uniqVars formula)] )
  where
    firstRow = intercalate "\t" (map (\v -> [v]) (uniqVars formula)) ++ "\tResult\n"
    rowString status = intercalate "\t" (map (\v -> showBool (calculator (Var v) status)) (uniqVars formula)) ++
                               "\t" ++ showBool (calculator formula status)


-- | Get all non-repeating propositional variables from a given formula
-- >>> uniqVars (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r')))
-- "pdqr"
uniqVars :: LogicFormula -> [Char]
uniqVars (Var v) = [v]      -- get propositional variable
uniqVars (Neg formula) = uniqVars formula
uniqVars (formula1 :/\ formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :\/ formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :-> formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :<-> formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars Bottom = []
uniqVars Top = []


-- | Generate a nested list of all possible variable assignments
-- >>> allPosStatus "pd"
-- [[('p',T),('d',T)],[('p',T),('d',F)],[('p',F),('d',T)],[('p',F),('d',F)]]
allPosStatus :: [Char] -> [[(Char, BoolValue)]]
allPosStatus [] = [[]]
allPosStatus (v:vs) = [(v, T):status | status <- rest] ++ [(v, F):status | status <- rest]
  where rest = allPosStatus vs


-- | Calculate the bool value of given formula and case status
-- >>> calculator (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r'))) [('p',T),('d',T),('q',T),('r',T)]
-- T
calculator :: LogicFormula -> [(Char, BoolValue)] -> BoolValue
calculator (Var v) status = fromMaybe (error ("Variable " ++ [v] ++ " Neg found in environment")) (lookup v status)
calculator (Neg formula) status = if calculator formula status == T then F else T
calculator (formula1 :/\ formula2) status = if calculator formula1 status == T && calculator formula2 status == T then T else F
calculator (formula1 :\/ formula2) status = if calculator formula1 status == F && calculator formula2 status == F then F else T
calculator (formula1 :-> formula2) status = if calculator formula1 status == T && calculator formula2 status == F then F else T
calculator (formula1 :<-> formula2) status = error "The formula is invalid."
calculator Bottom _ = F
calculator Top _ = T


