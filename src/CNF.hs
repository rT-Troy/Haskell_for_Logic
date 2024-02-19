module CNF where
--import Data.List.Split (splitOneOf)


data BoolValue = T | F deriving (Show, Eq)

data LogicFormula = Var Char    -- propositional variable
                   | Not LogicFormula
                   | LogicFormula :/\ LogicFormula
                   | LogicFormula :\/ LogicFormula
                   | LogicFormula :-> LogicFormula
                   | Bottom
                   | Top
                       deriving (Show, Eq)

-- toClause (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ Var 'd'))
-- toClause (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ (Not (Var 'd'))))
-- [Var 'p',Var 'q',Var 'r' :\/ Var 'd']
toClause :: LogicFormula -> [LogicFormula]-- -> BoolValue
toClause (clause1 :/\ clause2) = toClause clause1 ++ [clause2]
toClause clause1 = [clause1]

-- eachClause [Var 'p',Var 'q',Var 'r' :\/ Not (Var 'd')]
eachClause :: [LogicFormula] -> [LogicFormula]
eachClause [] = []
eachClause (clause:clauses) = toLiteral clause ++ eachClause clauses

-- toLiteral (Var 'r' :\/ Not (Var 'd'))
toLiteral :: LogicFormula -> [LogicFormula]
toLiteral (literal1 :\/ literal2) = toLiteral literal1 ++ [literal2]
toLiteral literal1 = [literal1]
