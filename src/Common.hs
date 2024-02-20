-- | Commom definition
module Common where

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