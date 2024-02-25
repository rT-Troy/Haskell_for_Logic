-- | Task 2 - Implementing CNF algorithm and DPLL algorithm using Haskell functions
module CNF where
--import Data.List.Split (splitOneOf)
import Data.List
import Text.PrettyPrint


import Common

-- step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
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
-- (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
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


-- step4elim ([Neg (Var 'q'),Var 'q',Var 'r'])
step4elim :: [LogicFormula] -> [LogicFormula]
step4elim [] = []
step4elim (x:xs)
    | revneg x `elem` xs = step4elim (filter (\y -> y /= x && y /= revneg x) xs)
    | otherwise = x : step4elim xs
    where revneg :: LogicFormula -> LogicFormula
          revneg (Neg l) = l
          revneg l = Neg l

-- cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
cnfAlgo :: LogicFormula -> [[LogicFormula]]
cnfAlgo formula = step4 (step3 (step2 (step1 formula)))

-- cnfPrint ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) [[]]
cnfPrint :: LogicFormula -> Doc
cnfPrint formula  = text "The given formula is:\n" <+>
                           formulaExpre formula <+>
                           text "\n\nThe clause set is:\n" <+>
                           text "{" <+> clausesPrint (cnfAlgo formula) <+> text "}"
                   
clausesPrint :: [[LogicFormula]] -> Doc
clausesPrint [] = text ""
clausesPrint [x] = text "{" <+> literalPrint x <+> text "}"
clausesPrint (x:xs) = text "{" <+> literalPrint x <+> text "}, " <+> clausesPrint xs

literalPrint :: [LogicFormula] -> Doc
literalPrint [] = text ""
literalPrint [x] = formulaExpre x
literalPrint (x:xs) = formulaExpre x <+> text "," <+> literalPrint xs

-- step4delsub [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']]
-- step4delsub [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r'],[Var 'r'],[Var 'q', Var 'r']]
-- The occurrence of duplicate variables was considered
step4delsub ::  [[LogicFormula]] -> [[LogicFormula]]
step4delsub [] = []
step4delsub (x:xs)
    | any (\b -> isSubsetOf b x && isSubsetOf x b) xs = error "should not have repeated variable"
    | any (\b -> isSubsetOf x b) xs = step4delsub xs
    | otherwise = x : step4delsub xs
    where isSubsetOf :: [LogicFormula] -> [LogicFormula] -> Bool
          isSubsetOf a b = all (\y -> y `elem` b) a

-- step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r')))
-- [[Neg (Var 'p'),Var 'q',Var 'r']]
step4 :: LogicFormula -> [[LogicFormula]]
step4 list = step4delsub (reverse (step4delsub (map step4elim (eachClause (toClause list)))))

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