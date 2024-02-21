-- | Task 2 - Implementing CNF algorithm and DPLL algorithm using Haskell functions
module CNF where
--import Data.List.Split (splitOneOf)
import Data.List

import Common

-- step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- step1 (Var 'q' :<-> (Var 'r' :<-> Var 'p'))
step1 :: LogicFormula -> LogicFormula
step1 (f1 :-> f2) = (step1 (Neg f1)) :\/ (step1 f2)
step1 (f1 :<-> f2) = (step1 (step1 f1 :-> step1 f2)) :/\ (step1 (step1 f2 :-> step1 f1))
step1 (Neg f) = (Neg (step1 f))
step1 (f1 :/\ f2) = (step1 f1 :/\ step1 f2)
step1 (f1 :\/ f2) = (step1 f1 :\/ step1 f2)
step1 Bottom = Bottom
step1 Top = Top
step1 f = f

-- step2 (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r'))
step2 :: LogicFormula -> LogicFormula
step2 (Neg (Neg f)) = step2 f
step2 (Neg (f1 :/\ f2)) = (step2 (Neg f1) :\/ step2 (Neg f2))
step2 (Neg (f1 :\/ f2)) = (step2 (Neg f1) :/\ step2 (Neg f2))
step2 (Neg Bottom) = Top
step2 (Neg Top) = Bottom
step2 (Neg f) = (Neg (step2 f))
step2 (f1 :/\ f2) = (step2 f1 :/\ step2 f2)
step2 (f1 :\/ f2) = (step2 f1 :\/ step2 f2)
step2 (f1 :-> f2) = error "step1 has bug"
step2 (f1 :<-> f2) = error "step1 has bug"
step2 f = f


-- step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r'))
step3 :: LogicFormula -> LogicFormula
step3 (x :\/ (y :/\ z)) = (step3 x :\/ step3 y) :/\ (step3 x :\/ step3 z)
step3 ((x :/\ y) :\/ z) = (step3 x :\/ step3 z) :/\ (step3 y :\/ step3 z)
step3 (Neg f) = Neg (step3 f)
step3 (f1 :/\ f2) = (step3 f1) :/\ (step3 f2)
step3 (f1 :\/ f2) = (step3 f1) :\/ (step3 f2)
step3 (_ :-> _) = error "step1 has bug"
step3 (_ :<-> _) = error "step1 has bug"
step3 Bottom = Bottom
step3 Top = Top
step3 f = f


-- (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
step4 :: [LogicFormula] -> LogicFormula
step4 f = toClause f

-- step41 ([Neg (Var 'q'),Var 'q',Var 'r'])
step41 :: [LogicFormula] -> [LogicFormula]
step41 [] = []
step41 (x:xs)
    | revneg x `elem` xs = step41 (filter (\y -> y /= x && y /= revneg x) xs)
    | otherwise = x : step41 xs
    where revneg :: LogicFormula -> LogicFormula
          revneg (Neg l) = l
          revneg l = Neg l


-- getCNF ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
getCNF :: LogicFormula -> LogicFormula
getCNF formula = step3 (step2 (step1 formula))

-- TEST: (¬p∨q∨r)∧(¬p∨r)∧¬q
-- toClause (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ Var 'd'))
-- toClause (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q')))
-- [Var 'p',Var 'q',Var 'r' :\/ Var 'd']
toClause :: LogicFormula -> [LogicFormula]
toClause (clause1 :/\ clause2) = toClause clause1 ++ toClause clause2
toClause clause = [clause]


-- eachClause [Var 'p',Var 'q',Var 'r' :\/ Neg (Var 'd')]
-- eachClause [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')]
eachClause :: [LogicFormula] -> [LogicFormula]
eachClause [] = []
eachClause (clause:clauses) = eachLiteral clause ++ eachClause clauses


-- eachLiteral (Var 'r' :\/ Neg (Var 'd'))
-- eachLiteral ((Neg (Var 'p') :\/ Var 'q') :\/ Var 'r')
eachLiteral :: LogicFormula -> [LogicFormula]
eachLiteral (literal1 :\/ literal2) = eachLiteral literal1 ++ eachLiteral literal2
eachLiteral literal = [literal]


-- toLiteral (Var 'p' :/\ Var 'q' :/\ (Var 'r' :\/ Var 'd'))
-- toLiteral (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q')))
toLiteral :: LogicFormula -> [LogicFormula]
toLiteral formula = nub (eachClause (toClause formula))
