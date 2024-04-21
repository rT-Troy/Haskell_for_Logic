{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
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
module CNF  ( cnfPrint
            , cnfAlgo
            , iffSplit
            , step1imp
            , step1
            , step2
            , step3imp
            , step4
            , step4delsub
            , step4elim
            , toClauseSets
            , splitConj
            , splitDisj
  ) where
import Data.List ( sortOn )
import Text.PrettyPrint ( Doc, (<+>), text )
import Data.List.Split ( splitOn )
import Common


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
                    formulaExpre afterstep3imp <+>
                    text "\n\nStep 4, the clause set is:\n" <+>
                    text "{" <+> clausesPrint afterStep4 <+> text "}\n"
                where afterStep1 = step1 formula
                      afterStep2 = step2 afterStep1
                      afterstep3imp = iffSplit formula
                      afterStep4 = step4 (iffSplit formula)


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
cnfAlgo formula = step4 (iffSplit formula)


-- | CNF iffSplit: eliminate iff ↔ from the input formula to implication,
-- |  then implement step1 to step3imp for each implication.
--
-- Example:
--
-- > $ iffSplit ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r'))
-- > ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) :/\ ((Neg (Var 'q') :\/ (Var 'p' :\/ Var 'q')) :/\ (Neg (Var 'r') :\/ (Var 'p' :\/ Var 'q')))
iffSplit :: LogicFormula -> LogicFormula
iffSplit (Neg (f1 :<-> f2)) = step2 ((Neg (step3imp (step2 (step1imp (iffSplit f1 :-> iffSplit f2))))) :/\ (Neg (step3imp (step2 (step1imp (iffSplit f2 :-> iffSplit f1))))))
iffSplit (f1 :<-> f2) = step3imp (step2 (step1imp (iffSplit f1 :-> iffSplit f2))) :/\ step3imp (step2 (step1imp (iffSplit f2 :-> iffSplit f1)))
iffSplit f = step3imp (step2 (step1imp f))    -- iffSplit (f1 :-> f2) = [[step1imp (f1 :-> f2)]]


-- | CNF step1imp: eliminate iff ↔ and implication → from the input formula.
--
-- Example:
--
-- > $ step1imp ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
-- > $ step1imp ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q'))
step1imp :: LogicFormula -> LogicFormula
step1imp (f1 :-> f2) = step1imp (Neg f1) :\/ step1imp f2
step1imp (Neg f) = Neg (step1imp f)
step1imp (f1 :/\ f2) = step1imp f1 :/\ step1imp f2
step1imp (f1 :\/ f2) = step1imp f1 :\/ step1imp f2
step1imp Bottom = Bottom
step1imp Top = Top
step1imp f = f


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
step1 (f1 :-> f2) = (step1 (Neg f1)) :\/ (step1 f2)
step1 (f1 :<-> f2) = (step1 (step1 f1 :-> step1 f2)) :/\ (step1 (step1 f2 :-> step1 f1))
step1 (Neg f) = (Neg (step1 f))
step1 (f1 :/\ f2) = (step1 f1 :/\ step1 f2)
step1 (f1 :\/ f2) = (step1 f1 :\/ step1 f2)
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
step2 (Neg (f1 :/\ f2)) = step2 (Neg f1) :\/ step2 (Neg f2)
step2 (Neg (f1 :\/ f2)) = step2 (Neg f1) :/\ step2 (Neg f2)
step2 (Neg Bottom) = Top
step2 (Neg Top) = Bottom
step2 (Neg f) = Neg (step2 f)
step2 (f1 :/\ f2) = step2 f1 :/\ step2 f2
step2 (f1 :\/ f2) = step2 f1 :\/ step2 f2
step2 (_ :-> _) = error "There should have no -> notation, make sure the fomula has been processed by step1."
step2 (_ :<-> _) = error "There should have no <-> notation, make sure the fomula has been processed by step1."
step2 f = f


-- | CNF step3imp: distribute disjunctions ∨ into conjunctions ∧.
-- | Do not accept the original formula involving iff ↔.
--
-- Example:
--
-- > $ step3imp ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
-- >
-- > $ step3imp (((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'q' :\/ Var 'r') :/\ (Neg (Var 'p') :/\ Neg (Var 'q'))))
-- > (((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ (Var 'q' :\/ Var 'r')) :/\ (((Var 'p' :\/ Var 'q') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ (Neg (Var 'p') :/\ Neg (Var 'q')))
-- >
-- > $ step3imp ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
-- > ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
step3imp :: LogicFormula -> LogicFormula
step3imp (x :\/ (y :/\ z)) = step3imp (step3imp(step3imp x :\/ step3imp y) :/\ step3imp(step3imp x :\/ step3imp z))
step3imp ((x :/\ y) :\/ z) = step3imp (step3imp(step3imp x :\/ step3imp z) :/\ step3imp(step3imp y :\/ step3imp z))
step3imp (Neg f) = Neg (step3imp f)
step3imp (_ :-> _) = error "There should have no -> notation, make sure the fomula has been processed by step1imp."
step3imp (_ :<-> _) = error "There should have no <-> notation, make sure the fomula has been processed by step1imp."
step3imp f = f


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
step4 list = step4delsub (sortOn length (map step4elim clauseSets))   -- ^ sortOn: make the shortest clause in the front
    where clauseSets = sortOn length (toClauseSets list)


-- | The occurrence of duplicate variables was considered.
--
-- Example:
--
-- > $ step4delsub [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']]
-- > [[Neg (Var 'p'),Var 'q',Var 'r']]
step4delsub ::  [[LogicFormula]] -> [[LogicFormula]]
step4delsub [] = []
step4delsub (x:xs)
    | any (\b -> isSubsetOf x b) xs = step4delsub xs
    | otherwise = x : step4delsub xs
    where isSubsetOf :: [LogicFormula] -> [LogicFormula] -> Bool
          isSubsetOf a b = all (\y -> y `elem` b) a


-- | CNF step4: simplify resulting CNF-formulas by eliminating duplicate literals in a clause.
--
-- Example:
--
-- > $ step4elim ([Neg (Var 'q'),Var 'q',Var 'r'])
-- > [Var 'r']
step4elim :: [LogicFormula] -> [LogicFormula]
step4elim [] = []
step4elim (x:xs)
    | revNeg x `elem` xs = step4elim (filter (\y -> y /= x && y /= revNeg x) xs)
    | otherwise = x : step4elim xs


-- | Convert a CNF formula to a list of clauses,
-- |  then convert each clause to a list of literals.
-- Example:
--
-- > $ toClauseSets ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')))
-- > [[Neg (Var 'p'),Var 'p',Var 'q',Var 'r'],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r']]
toClauseSets :: LogicFormula -> [[LogicFormula]]
toClauseSets formula = map (map strToLogicFormula) (toClausesString (stringFilter formula))


toClausesString :: String -> [[String]]
toClausesString formula = map splitDisj (splitConj formula)


splitConj :: String -> [String]
splitConj clause = splitOn ":/\\" clause


splitDisj :: String -> [String]
splitDisj clause = splitOn ":\\/" clause


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