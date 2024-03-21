{-|
Module      : DPLL
Description : Implementing DPLL algorithm and DPLL algorithm using Haskell functions
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module DPLL where
    
import Data.List

import Common
import CNF

-- -- | DPLL resuiting [] means unsatisfiable
-- dpllAlgo :: LogicFormula -> [[LogicFormula]]
-- dpllAlgo formula 
--         | length (head clauses) == 1 = chooseClause clauses
--         | otherwise = 
--         where clauses = chooseClause (calClause formula)

splitDPLL :: [[LogicFormula]] -> [[LogicFormula]]
splitDPLL [] = []

calClause :: LogicFormula -> [[LogicFormula]]
calClause formula = sortOn length (eachClause (toClause (step2 (step1 formula))))

chooseClause :: [[LogicFormula]] -> [[LogicFormula]]
chooseClause [] = []
chooseClause (x:xs)
        | isUnit x = chooseClause (elimDPLL (head x) xs)
        | otherwise = chooseClause xs
    where isUnit :: [LogicFormula] -> Bool
          isUnit clause = length clause == 1
          

elimDPLL :: LogicFormula -> [[LogicFormula]] -> [[LogicFormula]]
elimDPLL x [] = []
elimDPLL x (y:ys)
        | x `elem` y = elimDPLL x ys
        | revneg x `elem` y = filter (\z -> z /= x && z /= revneg x) y : elimDPLL x ys
        | otherwise = y : elimDPLL x ys
    where revneg :: LogicFormula -> LogicFormula
          revneg (Neg l) = l
          revneg l = Neg l
