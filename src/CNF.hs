module CNF where
--import Data.List.Split (splitOneOf)
import Data.List (nub)

data BoolValue = T | F deriving (Show, Eq)

data LogicFormula = Var Char    -- propositional variable
                   | Not LogicFormula
                   | LogicFormula :/\ LogicFormula
                   | LogicFormula :\/ LogicFormula
                   | LogicFormula :-> LogicFormula
                   | Bottom
                   | Top
                       deriving (Show, Eq)


-- test: (¬p∨q∨r)∧(¬p∨r)∧¬q


-- toClause (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ Var 'd'))
-- toClause (((Not (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Not (Var 'p')) :\/ Var 'r') :/\ (Not (Var 'q')))
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