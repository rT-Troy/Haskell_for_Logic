{-# OPTIONS_GHC -fno-warn-unused-imports -Wno-incomplete-patterns #-}
{-|
Module      : CNF
Description : Implementing Conjunctive Normal Form (CNF) algorithm and DPLL algorithm using Haskell functions
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module CNF  ( cnfPrint, cnfAlgo, step1, step2, step3, step4, toClauses, strToLogicFormula,
              step4delsub, step4Cpmtr, checkTautologicals, checkTautological,
              removeTautological, step4elim, stringFilter, toClausesString, 
              splitConj, splitDisj) where
import Data.List ( sortOn, nub)
import Text.PrettyPrint ( Doc, (<+>), text )
import Data.List.Split ( splitOn )
import Common
    ( clausesPrint, formulaExpre, revNeg, LogicFormula(..) )


-- | Main function: Implementing CNF algorithm in pretty print.
--
-- Example:
--
-- > $ cnfPrint ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > 
-- > ===Apply CNF algorithm to a formula===
-- > 
-- >  The given formula is:
-- >  ((p ∨ q) → (q ∨ r)) 
-- > 
-- > Step 1:
-- >  ((¬ (p ∨ q)) ∨ (q ∨ r)) 
-- > 
-- > Step 2:
-- >  (((¬ p) ∧ (¬ q)) ∨ (q ∨ r)) 
-- > 
-- > Step 3:
-- >  (((¬ p) ∨ (q ∨ r)) ∧ ((¬ q) ∨ (q ∨ r))) 
-- > 
-- > Step 4, the clause set is:
-- >  { { (¬ p) , q , r } }
cnfPrint :: LogicFormula -> Doc
cnfPrint formula  = text "\n===Apply CNF algorithm to a formula===\n\n" <+>
                    text "The given formula is:\n" <+>
                    formulaExpre formula <+>
                    text "\n\nStep 1:\n" <+>
                    formulaExpre afterStep1 <+>
                    text "\n\nStep 2:\n" <+>
                    formulaExpre afterStep2 <+>
                    text "\n\nStep 3:\n" <+>
                    formulaExpre afterstep3 <+>
                    text "\n\nStep 4, the clause set is:\n" <+>
                    text "{" <+> clausesPrint afterStep4 <+> text "}\n"
                where afterStep1 = step1 formula
                      afterStep2 = step2 afterStep1
                      afterstep3 = step3 afterStep2
                      afterStep4 = cnfAlgo formula


-- | Implementing CNF algorithm following the step 1 to step 4.
--
-- Example:
--
-- > $ cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
-- >
-- > $ cnfAlgo ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r'))
-- > [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'r'),Var 'p',Var 'q']]
cnfAlgo :: LogicFormula -> [[LogicFormula]]
cnfAlgo formula = step4 (step3 (step2 (step1 formula)))


-- | CNF step1: eliminate iff ↔ and implication → from the input formula.
--
-- Example:
--
-- > $ step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
-- >
-- > $ step1 (Neg ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r')))
-- > Neg ((Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q')))
step1 :: LogicFormula -> LogicFormula
step1 (f1 :<-> f2) =  step1 (step1 f1 :-> step1 f2) :/\ step1 (step1 f2 :-> step1 f1)
step1 (f1 :-> f2) =  step1 (revNeg f1) :\/ step1 f2
step1 (Neg f) =  revNeg (step1 f)
step1 (f1 :/\ f2)
    | f1 == revNeg f2 = Bottom
    | otherwise =  step1 f1 :/\ step1 f2
step1 (f1 :\/ f2) =  step1 f1 :\/ step1 f2
step1 Bottom = Bottom
step1 Top = Top
step1 f = f


-- | CNF step2: push negations ¬ towards literals.
--
-- Example:
--
-- > $ step2 ((Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')))
-- > (Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')
-- >
-- > $ step2 (Neg ((Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q'))))
-- >
-- > $ step2 ((Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q')))
-- > ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
step2 :: LogicFormula -> LogicFormula
step2 (Neg (Neg f)) = step2 f
step2 (Neg (f1 :/\ f2))
                        | f1 == revNeg f2 = Top
                        | otherwise = step2 (Neg f1) :\/ step2 (Neg f2)
step2 (Neg (f1 :\/ f2)) = step2 (Neg f1) :/\ step2 (Neg f2)
step2 (f1 :/\ f2)
                        | f1 == revNeg f2 = Bottom
                        | otherwise = step2 f1 :/\ step2 f2
step2 (f1 :\/ f2) = step2 f1 :\/ step2 f2
step2 (Neg Bottom) = Top
step2 (Neg Top) = Bottom
step2 (Neg f) = Neg (step2 f)
step2 (_ :-> _) = error "Error: '->' notation detected. Ensure the formula has been processed by 'step1'."
step2 (_ :<-> _) = error "Error: '<->' notation detected. Ensure the formula has been processed by 'step1'."
step2 f = f


checkCNF :: LogicFormula -> LogicFormu

-- | CNF step3: distribute disjunctions ∨ into conjunctions ∧.
-- | Do not accept the original formula involving iff ↔.
--
-- Example:
--
-- > $ step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
-- >
-- > $ step3 (((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'q' :\/ Var 'r') :/\ (Neg (Var 'p') :/\ Neg (Var 'q'))))
-- > (((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ (Var 'q' :\/ Var 'r')) :/\ (((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ (Neg (Var 'p') :/\ Neg (Var 'q')))
-- >
-- > $ step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
-- > ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
step3 :: LogicFormula -> LogicFormula
step3 f@((a :/\ b) :\/ (c :/\ d)) = step3Dis (a :/\ b) :\/ step3Dis (c :/\ d)    -- The case of DNF :/\ :\/.
step3 f@(x :\/ (y :/\ z)) = step3Con f
step3 f@((x :/\ y) :\/ z) = step3Con f
step3 (x :\/ y) = step3 x :\/ step3 y
step3 (x :/\ y) = step3 x :/\ step3 y
step3 (Neg f) = revNeg (step3 f)
step3 (_ :-> _) = error "Error: '->' notation detected. Ensure the formula has been processed by 'step1'."
step3 (_ :<-> _) = error "Error: '<->' notation detected. Ensure the formula has been processed by 'step1'."
step3 f = f

step3Con :: LogicFormula -> LogicFormula
step3Con (x :\/ (y :/\ z)) = step3Con (step3Con (step3Con (step3Con x :\/ step3Con y) :/\ step3Con (step3Con x :\/ step3Con z)))
step3Con ((x :/\ y) :\/ z) = step3Con (step3Con (step3Con (step3Con x :\/ step3Con z) :/\ step3Con (step3Con y :\/ step3Con z)))
step3Con f = f

step3Dis :: LogicFormula -> LogicFormula
step3Dis (x :/\ (y :\/ z)) =  step3Dis (step3Dis (step3Dis x :/\ step3Dis y) :\/ step3Dis (step3Dis x :/\ step3Dis z))
step3Dis ((x :\/ y) :/\ z) =  step3Dis (step3Dis (step3Dis x :/\ step3Dis z) :\/ step3Dis (step3Dis y :/\ step3Dis z))
step3Dis f = f

dnfToCnf :: LogicFormula -> LogicFormula
dnfToCnf (x :\/ (y :/\ z)) = dnfToCnf (dnfToCnf (dnfToCnf (dnfToCnf x :\/ dnfToCnf y) :/\ dnfToCnf (dnfToCnf x :\/ dnfToCnf z)))
dnfToCnf ((x :/\ y) :\/ z) = dnfToCnf (dnfToCnf (dnfToCnf (dnfToCnf x :\/ dnfToCnf z) :/\ dnfToCnf (dnfToCnf y :\/ dnfToCnf z)))
dnfToCnf f = f

-- > $ cnfDistributive [[Var 'p',Var 'q'],[Neg (Var 'q')],[Neg (Var 'r')]] [[Var 'q',Var 'r'],[Neg (Var 'p')],[Neg (Var 'q')]]
-- > [[Var 'p',Var 'q',Var 'q',Var 'r'],[Var 'p',Var 'q',Neg (Var 'p')],[Var 'p',Var 'q',Neg (Var 'q')],
-- >  [Neg (Var 'q'),Var 'q',Var 'r'],[Neg (Var 'q'),Neg (Var 'p')],[Neg (Var 'q'),Neg (Var 'q')],[Neg (Var 'r'),Var 'q',Var 'r'],[Neg (Var 'r'),Neg (Var 'p')],[Neg (Var 'r'),Neg (Var 'q')]]
cnfDistributive :: [[LogicFormula]] -> [[LogicFormula]] -> [[LogicFormula]]
cnfDistributive [] _ = []
cnfDistributive (x:xs) y = cnfEachDistri x y ++ cnfDistributive xs y

cnfEachDistri :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]]
cnfEachDistri _ [] = []
cnfEachDistri x (y:ys) = (x ++ y) : cnfEachDistri x ys

-- | CNF step4: simplify resulting CNF-formulas by removing duplicate literals.
--
-- Example:
--
-- > $ step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r')))
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
-- >
-- > $ step4 (((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q')))
-- > [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'q') :/\ Neg (Var 'r'),Var 'p',Var 'q']]
step4 :: LogicFormula -> [[LogicFormula]]
--step4 ((a :/\ b) :\/ (c :/\ d)) = step4delsub (sortOn length (step4Cpmtr (map step4elim (sortOn length nextCNFClauses))))-- step4delsub (sortOn length (step4Cpmtr (map step4elim (sortOn length newCNFClauses))))
--    where nextCNFClauses = cnfDistributive (toDisj (a :/\ b)) (toDisj (c :/\ d)) 
step4 list@(_ :/\ _) = step4delsub (sortOn length (step4Cpmtr (map step4elim (sortOn length (toClauses list)))))   -- ^ sortOn: make the shortest clause in the front
step4 list@(_ :\/ _) = step4delsub (sortOn length (step4Cpmtr (filter (not . null) (map dnf4elim (sortOn length (toDisjClauses list))))))

-- | Removing the clauses if it is a subset of another clause in the clause set.
--
-- Example:
--
-- > $ step4delsub [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']]
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
step4delsub ::  [[LogicFormula]] -> [[LogicFormula]]
step4delsub [] = []
step4delsub clauses@(x:xs)
    | clauses == [[Top]] = [[Top]]  -- only one clause {⊤}
    | Bottom `elem` x = error "Error: 'Bottom' notation detected. Ensure the formula has been processed by 'step4elim'."  -- φ ∧ ⊥ = ⊥
    | Top `elem` x = step4delsub xs -- φ ∨ ⊤ = ⊤, φ ∧ ⊤ = φ, T is in the clause set, remove the entire clause
    | any (\y -> all (`elem` y) x) xs = step4delsub xs
    | otherwise = x : step4delsub xs


-- | Remove the tautological clauses in a clause set.
-- | Such as for CNF: ((¬ r) ∨ ((¬ q) ∨ p))) ∧ ((q ∨ ((¬ p) ∨ r)) = T.
-- | DNF: ((¬ r) ∧ ((¬ q) ∧ p))) ∨ ((q ∧ ((¬ p) ∧ r)) = F.
-- | ((p → r) ↔ (q → p))
step4Cpmtr :: [[LogicFormula]] -> [[LogicFormula]]
step4Cpmtr [] = []
step4Cpmtr (x:xs)
    | checkTautologicals x xs = step4Cpmtr (removeTautological x xs)
    | otherwise = x : step4Cpmtr xs


-- | Check if exists tautological clause in a clause set.
checkTautologicals :: [LogicFormula] -> [[LogicFormula]] -> Bool
checkTautologicals _ [] = False
checkTautologicals x (y:ys)
    | checkTautological x x y y = True
    | otherwise = checkTautologicals x ys



checkTautological :: [LogicFormula] -> [LogicFormula] -> [LogicFormula] -> [LogicFormula] -> Bool
checkTautological [] _ [] _ = True
checkTautological (x:xs) orixss (y:ys) oriyss
    | length orixss /= length oriyss = False
    | revNeg x `elem` oriyss && revNeg y `elem` orixss = checkTautological xs orixss ys oriyss
    | otherwise = False


-- | Remove the tautological clause in a clause set.
removeTautological :: [LogicFormula] -> [[LogicFormula]] -> [[LogicFormula]]
removeTautological _ [] = []
removeTautological x (y:ys)
    | checkTautological x x y y = removeTautological x ys
    | otherwise = y : removeTautological x ys

-- | Removing the duplicate literals and tautological literals such as p and ¬p in the same clause.
--
-- Example:
--
-- > $ step4elim ([Neg (Var 'q'),Var 'q',Var 'r',Var 'r'])
-- > [Var 'r']
step4elim :: [LogicFormula] -> [LogicFormula]
step4elim [] = []
step4elim literals@(x:xs)
    | Top `elem` literals || revNeg x `elem` xs = [Top]  -- ^ p ∨ ¬ p = ⊤, φ ∨ ⊤ = ⊤, so if tautological literals exist or ⊤ exists, only keep ⊤.
    | Bottom `elem` literals = step4elim (filter (/= Bottom) literals)  -- ^ φ ∨ ⊥ = φ, so remove ⊥ in the clause
    | x `elem` xs = step4elim (nub literals)    -- ^ remove duplicate literals
    | otherwise = x : step4elim xs


dnf4elim :: [LogicFormula] -> [LogicFormula]
dnf4elim [] = []
dnf4elim literals@(x:xs)
    | Bottom `elem` literals || revNeg x `elem` xs = step4elim xs    -- ^ p ∧ ¬ p = ⊥, φ ∧ ⊥ = ⊥, could be ignored, so remove the entire clause.
    | Top `elem` literals = step4elim (filter (/= Bottom) literals)    -- ^ , φ ∧ ⊤ = φ, so if tautological literals exist or ⊤ exists, only keep ⊤.
    | x `elem` xs = step4elim (nub literals)    -- ^ remove duplicate literals
    | otherwise = x : step4elim xs

-- | Convert a CNF formula to a list of clauses,
-- |  then convert each clause to a list of literals.
-- Example:
--
-- > $ toClauses ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')))
-- > [[Neg (Var 'p'),Var 'p',Var 'q',Var 'r'],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r']]
toClauses :: LogicFormula -> [[LogicFormula]]
toClauses formula = map (map strToLogicFormula) (toClausesString (stringFilter formula))


toClausesString :: String -> [[String]]
toClausesString formula = map splitDisj (splitConj formula)


-- > $ toDisj ((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r')))
-- > [[Var 'p',Var 'q'],[Neg (Var 'q')],[Neg (Var 'r')]]
-- > $ toDisj ((Var 'q' :\/ Var 'r') :/\ (Neg (Var 'p') :/\ Neg (Var 'q')))
-- > [[Var 'q',Var 'r'],[Neg (Var 'p')],[Neg (Var 'q')]]
toDisjClauses :: LogicFormula -> [[LogicFormula]]
toDisjClauses formula =  map (map strToLogicFormula) (toClausesString (stringFilter formula))

toDisjString :: String -> [[String]]
toDisjString formula =  map splitConj (splitDisj formula)


splitConj :: String -> [String]
splitConj = splitOn ":/\\"


splitDisj :: String -> [String]
splitDisj = splitOn ":\\/"


stringFilter :: LogicFormula -> String
stringFilter (Var c) = "Var '" ++ [c] ++ "'"
stringFilter (Neg f) = "Neg (" ++ stringFilter f ++ ")"
stringFilter (f1 :/\ f2) = stringFilter f1 ++ " :/\\ " ++ stringFilter f2
stringFilter (f1 :\/ f2) = stringFilter f1 ++ " :\\/ " ++ stringFilter f2
stringFilter (f1 :-> f2) = stringFilter f1 ++ " :-> " ++ stringFilter f2
stringFilter (f1 :<-> f2) = stringFilter f1 ++ " :<-> " ++ stringFilter f2
stringFilter Bottom = "Bottom"
stringFilter Top = "Top"


strToLogicFormula :: String -> LogicFormula
strToLogicFormula formula = read formula :: LogicFormula