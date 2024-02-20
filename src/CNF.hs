{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Task 2 - Implementing CNF algorithm and DPLL algorithm using Haskell functions
module CNF () where
--import Data.List.Split (splitOneOf)
import Data.List

-- | define the boolvalue type

data BoolValue = T | F deriving (Show, Eq)

-- | Basic well-formed rules defination
data LogicFormula = Var Char                          -- propositional variable
                   | Neg LogicFormula                 -- ¬ φ
                   | LogicFormula :/\ LogicFormula    -- φ ∧ ψ
                   | LogicFormula :\/ LogicFormula    -- φ ∨ ψ
                   | LogicFormula :-> LogicFormula    -- φ → ψ
                   | LogicFormula :<-> LogicFormula   -- φ ↔ ψ
                   | Bottom                           -- ⊥
                   | Top                              -- ⊤
                       deriving (Show, Eq)

-- TEST: (¬p∨q∨r)∧(¬p∨r)∧¬q
-- toClause (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ Var 'd'))
-- >>> toClause (((Not (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Not (Var 'p')) :\/ Var 'r') :/\ (Not (Var 'q')))
-- [Var 'p',Var 'q',Var 'r' :\/ Var 'd']
toClause :: LogicFormula -> [LogicFormula]
toClause (clause1 :/\ clause2) = toClause clause1 ++ toClause clause2
toClause clause = [clause]


-- eachClause [Var 'p',Var 'q',Var 'r' :\/ Not (Var 'd')]
-- eachClause [(Not (Var 'p') :\/ Var 'q') :\/ Var 'r',Not (Var 'p') :\/ Var 'r',Not (Var 'q')]
eachClause :: [LogicFormula] -> [LogicFormula]
eachClause [] = []
eachClause (clause:clauses) = eachLiteral clause ++ eachClause clauses


-- eachLiteral (Var 'r' :\/ Not (Var 'd'))
-- eachLiteral ((Not (Var 'p') :\/ Var 'q') :\/ Var 'r')
eachLiteral :: LogicFormula -> [LogicFormula]
eachLiteral (literal1 :\/ literal2) = eachLiteral literal1 ++ eachLiteral literal2
eachLiteral literal = [literal]


-- toLiteral (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ Var 'd'))
-- toLiteral (((Not (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Not (Var 'p')) :\/ Var 'r') :/\ (Not (Var 'q')))
toLiteral :: LogicFormula -> [LogicFormula]
toLiteral formula = nub (eachClause (toClause formula))