-- | Task 2 - Implementing CNF algorithm and DPLL algorithm using Haskell functions
module CNF where
--import Data.List.Split (splitOneOf)
import Data.List
import Text.PrettyPrint


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
step2 (_ :-> _) = error "step1 has bug"
step2 (_ :<-> _) = error "step1 has bug"
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


-- step41 ([Neg (Var 'q'),Var 'q',Var 'r'])
step41 :: [LogicFormula] -> [LogicFormula]
step41 [] = []
step41 (x:xs)
    | revneg x `elem` xs = step41 (filter (\y -> y /= x && y /= revneg x) xs)
    | otherwise = x : step41 xs
    where revneg :: LogicFormula -> LogicFormula
          revneg (Neg l) = l
          revneg l = Neg l


step42 :: [[LogicFormula]] -> [[LogicFormula]]
step42 [] = []
step42 (x:xs) = step41 x : step42 xs

-- step4 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
step4 :: LogicFormula -> [[LogicFormula]]
step4 f = step45 (step42 (eachClause (toClause (step3 (step2 (step1 f))))))

-- step44 [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']]
-- step44 [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r'],[Var 'r'],[Var 'q', Var 'r']]
-- The occurrence of duplicate variables was considered
step44 ::  [[LogicFormula]] -> [[LogicFormula]]
step44 [] = []
step44 (x:xs)
    | any (\b -> isSubsetOf b x && isSubsetOf x b) xs = error "should not have repeated variable"
    | any (\b -> isSubsetOf x b) xs = step44 xs
    | otherwise = x : step44 xs
    where isSubsetOf :: [LogicFormula] -> [LogicFormula] -> Bool
          isSubsetOf a b = all (\y -> y `elem` b) a

-- step45 [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r'],[Var 'r'],[Var 'q', Var 'r']]
step45 :: [[LogicFormula]] -> [[LogicFormula]]
step45 list = step44 (reverse (step44 list))

-- cnfPrint :: [[LogicFormula]] -> Doc



-- TEST: (¬p∨q∨r)∧(¬p∨r)∧¬q
-- toClause (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q')))
toClause :: LogicFormula -> [LogicFormula]
toClause (clause1 :/\ clause2) = toClause clause1 ++ toClause clause2
toClause clause = [clause]


-- eachClause [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')]
eachClause :: [LogicFormula] -> [[LogicFormula]]
eachClause [] = []
eachClause (clause:clauses) = [eachLiteral clause] ++ eachClause clauses


-- eachLiteral ((Neg (Var 'p') :\/ Var 'q') :\/ Var 'r')
eachLiteral :: LogicFormula -> [LogicFormula]
eachLiteral (literal1 :\/ literal2) = eachLiteral literal1 ++ eachLiteral literal2
eachLiteral literal = [literal]


-- TODO: [LogicFormula]
-- toLiteral (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q')))
toLiteral :: LogicFormula -> [[LogicFormula]]
toLiteral formula = nub (eachClause (toClause formula))
