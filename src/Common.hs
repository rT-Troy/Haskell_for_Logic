-- |Commom definition
module Common where

import Text.PrettyPrint

-- | Define the boolvalue type
data BoolValue = T | F deriving (Show, Eq)


-- | Basic well-formed rules definition
data LogicFormula = Var Char                          -- ^ propositional variable
                   | Neg LogicFormula                 -- ^ ¬ φ
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
-- >>> formulaExpre ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r')))
-- ((p → (q → r)) → ((p → q) → (p → r)))
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

