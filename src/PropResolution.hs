{-|
Module      : PropResolution
Description : Propositional Resolution
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module PropResolution where

import Common


-- | Implementing propositional resolution to clause sets.
--
-- Example:
--
-- > $ resolClauses [[Var 'p',Var 'q'],[Var 'p',Neg (Var 'q')],[Neg (Var 'p'),Var 'q'],[Neg (Var 'p'),Neg (Var 'q')]]
-- > [Var 'p',Var 'q',Neg (Var 's')]
resolClauses :: [[LogicFormula]] -> [LogicFormula]
resolClauses [] = []
resolClauses (x:xs) = propResol x (resolClauses xs)

-- | Implementing propositional resolution rule.
-- It takes 2 clauses as input, combines them and eliminates the tautological literals in @propSolve@.
--
-- Example:
--
-- > $ propResol [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r']
-- > [Var 'p',Var 'q',Neg (Var 's')]
propResol :: [LogicFormula] -> [LogicFormula] -> [LogicFormula]
propResol clause1 clause2 = propSolve (clause1 ++ clause2)


-- | Eliminating the tautological literals in a combined literal list of 2 clauses.
--
-- Example:
--
-- > $ propSolve [Var 'p', Var 'q', Neg (Var 'r'), Neg (Var 's'), Var 'r']
-- > [Var 'p',Var 'q',Neg (Var 's')]
propSolve :: [LogicFormula] -> [LogicFormula]
propSolve [] = []
propSolve (x:xs)
    | revNeg x `elem` xs || x `elem` xs = propSolve (filter (\y -> y /= x && y /= revNeg x) xs)
    | otherwise = x : propSolve xs