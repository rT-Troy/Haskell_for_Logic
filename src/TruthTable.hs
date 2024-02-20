-- | Task 1 - construct truth tables for given formulas
module TruthTable () where

import Data.List
import Data.Maybe
import GHC.Show
import GHC.Types
import GHC.Classes
import GHC.Base
import Text.PrettyPrint


-- | define the boolvalue type
data BoolValue = T | F deriving (Show, Eq)

-- | Basic well-formed rules defination
data LogicFormula = Var Char                          -- propositional variable
                   | Neg LogicFormula                 -- ¬ φ
                   | LogicFormula :/\ LogicFormula    -- φ ∧ ψ
                   | LogicFormula :\/ LogicFormula    -- φ ∨ ψ
                   | LogicFormula :-> LogicFormula    -- φ → ψ
                   | Bottom                           -- ⊥
                   | Top                              -- ⊤
                       deriving (Show, Eq)


-- | main function
-- TEST:
-- truthTable ((Var 'q') :/\ (Var 'r'))
-- >>> formula = (Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r'))
-- >>> truthTable formula
-- The given formula is:
--  ((p → (q → r)) → ((p → q) → (p → r))) 
-- Truth table result:
--  p	q	r	Result
-- T	T	T	T
-- T	T	F	T
-- T	F	T	T
-- T	F	F	T
-- F	T	T	T
-- F	T	F	T
-- F	F	T	T
-- F	F	F	T
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
-- TEST:
-- >>> uniqVars (Var 'p' :\/ Var 'q')
-- >>> uniqVars (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r')))
-- "pq"
-- "pdqr"
uniqVars :: LogicFormula -> [Char]
uniqVars (Var v) = [v]      -- get propositional variable
uniqVars (Neg formula) = uniqVars formula
uniqVars (formula1 :/\ formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :\/ formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars (formula1 :-> formula2) = nub (uniqVars formula1 ++ uniqVars formula2)
uniqVars Bottom = []
uniqVars Top = []


-- | Generate a nested list of all possible variable assignments
-- TEST:
-- >>> variables = "pd"
-- >>> allPosStatus (variables)
allPosStatus :: [Char] -> [[(Char, BoolValue)]]
allPosStatus [] = [[]]
allPosStatus (v:vs) = [(v, T):status | status <- rest] ++ [(v, F):status | status <- rest]
  where rest = allPosStatus vs


-- | calculate the bool value of given formula and case status
-- TEST:
-- >>> arg = (((Var 'p') :\/ (Var 'd')) :-> ((Var 'q') :/\(Var 'r'))) [('p',T),('d',T),('q',T),('r',T)]
-- >>> calculator arg
calculator :: LogicFormula -> [(Char, BoolValue)] -> BoolValue
calculator (Var v) status = fromMaybe (error ("Variable " ++ [v] ++ " Neg found in environment")) (lookup v status)
calculator (Neg formula) status = if calculator formula status == T then F else T
calculator (formula1 :/\ formula2) status = if calculator formula1 status == T && calculator formula2 status == T then T else F
calculator (formula1 :\/ formula2) status = if calculator formula1 status == F && calculator formula2 status == F then F else T
calculator (formula1 :-> formula2) status = if calculator formula1 status == T && calculator formula2 status == F then F else T
calculator Bottom _ = F
calculator Top _ = T


-- | show value of Bool type to String
showBool :: BoolValue -> String
showBool T = "T"
showBool F = "F"

-- | Formula Print out in logic representation
formulaExpre :: LogicFormula -> Doc
formulaExpre (Var v) = text [v]
formulaExpre (Neg v) = parens (text "¬" <+> formulaExpre v)
formulaExpre (formula1 :/\ formula2) = parens (formulaExpre formula1 <+>
                                         text "∧" <+> formulaExpre formula2)
formulaExpre (formula1 :\/ formula2) = parens (formulaExpre formula1 <+>
                                         text "∨" <+> formulaExpre formula2)
formulaExpre (formula1 :-> formula2) = parens (formulaExpre formula1 <+>
                                         text "→" <+> formulaExpre formula2)
formulaExpre (Bottom) = text "⊥"
formulaExpre (Top) = text "⊤"
