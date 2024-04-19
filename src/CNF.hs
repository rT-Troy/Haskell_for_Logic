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
            , step1Each
            , step1
            , step2
            , step3
            , step4
            , step4delsub
            , step4elim
            , toClauseSets
            , splitConj
            , splitDisj
  ) where
import Data.List ( sortOn )
import Text.PrettyPrint ( Doc, (<+>), text )
--import Data.List.Split (splitOn)
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
                    formulaExpre afterStep3 <+>
                    text "\n\nStep 4, the clause set is:\n" <+>
                    text "{" <+> clausesPrint afterStep4 <+> text "}\n"
                where afterStep1 = step1 formula
                      afterStep2 = step2 afterStep1
                      afterStep3 = step3 afterStep2
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


iffSplit :: LogicFormula -> LogicFormula
iffSplit (f1 :<-> f2) = step3 (step2 (step1Each (f1 :-> f2))) :/\ step3 (step2 (step1Each (f2 :-> f1)))
iffSplit f = step3 (step2 (step1Each f))    -- iffSplit (f1 :-> f2) = [[step1Each (f1 :-> f2)]]

-- | CNF step1Each: eliminate iff ↔ and implication → from the input formula.
--
-- Example:
--
-- > $ step1Each ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
-- > $ step1Each ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q'))
step1Each :: LogicFormula -> LogicFormula
step1Each (f1 :-> f2) = step1Each (Neg f1) :\/ step1Each f2
step1Each (Neg f) = Neg (step1Each f)
step1Each (f1 :/\ f2) = step1Each f1 :/\ step1Each f2
step1Each (f1 :\/ f2) = step1Each f1 :\/ step1Each f2
step1Each Bottom = Bottom
step1Each Top = Top
step1Each f = f


-- | CNF step1: eliminate iff ↔ and implication → from the input formula.
--
-- Example:
--
-- > $ step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))
-- > Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
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


-- | CNF step3: distribute disjunctions ∨ into conjunctions ∧.
--
-- Example:
--
-- > $ step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r'))
-- > (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
-- >
-- > $ step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
-- > ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))
step3 :: LogicFormula -> LogicFormula
step3 ((a :\/ (b :/\ c)) :/\ (d :\/ (e :/\ f))) = ( a :\/  b :/\  a :\/  c) :/\ ( d :\/  e :/\  d :\/  f)
step3 (((a :/\ b) :\/ c) :/\ ((d :/\ e) :\/ f)) = ( a :\/  c :/\  b :\/  c) :/\ ( d :\/  f :/\  e :\/  f)
step3 (x :\/ (y :/\ z)) = (step3 x :\/ step3 y) :/\ (step3 x :\/ step3 z)
step3 ((x :/\ y) :\/ z) = (step3 x :\/ step3 z) :/\ (step3 y :\/ step3 z)
step3 (Neg f) = Neg (step3 f)
step3 (_ :-> _) = error "There should have no -> notation, make sure the fomula has been processed by step1Each."
step3 (_ :<-> _) = error "There should have no <-> notation, make sure the fomula has been processed by step1Each."
step3 Bottom = Bottom
step3 Top = Top
step3 f = f


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
step4 list = step4delsub (sortOn length (map step4elim (toClauseSets list)))   -- ^ sortOn: make the shortest clause in the front

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
-- > $ 
toClauseSets :: LogicFormula -> [[LogicFormula]]
toClauseSets expr = map splitDisj (splitConj expr)

splitConj :: LogicFormula -> [LogicFormula]
splitConj (f1 :/\ f2) = splitConj f1 ++ splitConj f2
splitConj formula = [formula]

splitDisj :: LogicFormula -> [LogicFormula]
splitDisj (f1 :\/ f2) = splitDisj f1 ++ splitDisj f2
splitDisj formula = [formula]