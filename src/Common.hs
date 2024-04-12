{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Common
Description : Common definitions for the project
Copyright   : 2024 Jun Zhang
License     : BSD-style (see LICENSE)
Maintainer  : yotroy@foxmail.com
Stability   : experimental
Portability : haskell 2010

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module Common where

import Text.PrettyPrint ( Doc, (<+>), parens, text )

-- | Define the boolvalue type
data BoolValue = T | F deriving (Show, Eq)


-- | Basic well-formed rules definition.
-- | 
data LogicFormula = Var Char                          -- ^ propositional variable 
                   | Neg LogicFormula                 -- ^ ¬ φ : negation    Neg (Var 'p')
                   | LogicFormula :/\ LogicFormula    -- ^ φ ∧ ψ
                   | LogicFormula :\/ LogicFormula    -- ^ φ ∨ ψ
                   | LogicFormula :-> LogicFormula    -- ^ φ → ψ
                   | LogicFormula :<-> LogicFormula   -- ^ φ ↔ ψ
                   | Bottom                           -- ^ ⊥
                   | Top                              -- ^ ⊤
                       deriving (Show, Eq)

-- | Show value of Bool type to String
showBool :: BoolValue -> String
showBool T = "T"
showBool F = "F"


-- | Formula Print out in logic representation
-- Example:
--
-- > $ formulaExpre ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r')))
-- > ((p → (q → r)) → ((p → q) → (p → r)))
formulaExpre :: LogicFormula -> Doc
formulaExpre (Var v) = text [v]
formulaExpre (Neg v) = parens (text "¬" <+> formulaExpre v)
formulaExpre (formula1 :/\ formula2) = parens (formulaExpre formula1 <+>
                                         text "∧" <+> formulaExpre formula2)
formulaExpre (formula1 :\/ formula2) = parens (formulaExpre formula1 <+>
                                         text "∨" <+> formulaExpre formula2)
formulaExpre (formula1 :-> formula2) = parens (formulaExpre formula1 <+>
                                         text "→" <+> formulaExpre formula2)
formulaExpre (formula1 :<-> formula2) = parens (formulaExpre formula1 <+>
                                         text "↔" <+> formulaExpre formula2)
formulaExpre (Bottom) = text "⊥"
formulaExpre (Top) = text "⊤"

-- | Definition of the negation for basic rules
revNeg :: LogicFormula -> LogicFormula
revNeg (Neg l) = l
revNeg l = Neg l


-- | Pretty print of the given clauses sets, calling literalPrint to print each clause.
--
-- Example:
--
-- > $ clausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
-- > { (¬ r) , (¬ p) , q },  { s , (¬ t) , (¬ p) },  { s , p , r },  { t , s , q },  { (¬ r) , (¬ p) , (¬ q) },  { s , t , r },  { p }
clausesPrint :: [[LogicFormula]] -> Doc
clausesPrint [] = text ""
clausesPrint [x] = text "{" <+> literalPrint x <+> text "}"
clausesPrint (x:xs) = text "{" <+> literalPrint x <+> text "}, " <+> clausesPrint xs


-- | Pretty print of the given literals.
--
-- Example:
--
-- > $ literalPrint [Neg (Var 'r'),Neg (Var 'p'),Var 'q']
literalPrint :: [LogicFormula] -> Doc
literalPrint [] = text "[]"
literalPrint [x] = formulaExpre x
literalPrint (x:xs) = formulaExpre x <+> text "," <+> literalPrint xs