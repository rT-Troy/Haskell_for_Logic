module CommonSpec (commonTests) where
import Test.Hspec

import Common

commonTests :: Spec
commonTests = describe "Common Tests" $ do

    it "BoolValue: can be shown" $ do
        show T `shouldBe` "T"
        show F `shouldBe` "F"

    it "BoolValue: can be equated" $ do
        T `shouldBe` T
        F `shouldBe` F
        F `shouldNotBe` T
        T `shouldNotBe` F

    it "LogicFormula: can be equated" $ do
        (Var 'p') `shouldBe` (Var 'p')
        (Var 'p') `shouldNotBe` (Neg (Var 'p'))

    it "LogicFormula: can be shown" $ do
        show (Var 'p') `shouldBe` "Var 'p'"
        show (Var 'p') `shouldNotBe` "Var 'q'"
        show Bottom `shouldBe` "Bottom"
        show (Var 'q') `shouldBe` "Var 'q'"

    it "showBool: convert BoolValue to String" $ do
        showBool T `shouldBe` "T"
        showBool F `shouldBe` "F"

    it "formulaExpre: convert LogicFormula to Doc" $ do
        show (formulaExpre (Var 'p')) `shouldBe` "p"
        show (formulaExpre (Neg (Var 'p'))) `shouldBe` "(¬ p)"
        show (formulaExpre (Var 'p' :/\ Var 'q')) `shouldBe` "(p ∧ q)"
        show (formulaExpre (Var 'p' :\/ Var 'q')) `shouldBe` "(p ∨ q)"
        show (formulaExpre (Var 'p' :-> Var 'q')) `shouldBe` "(p → q)"
        show (formulaExpre (Var 'p' :<-> Var 'q')) `shouldBe` "(p ↔ q)"
        show (formulaExpre Bottom) `shouldBe` "⊥"
        show (formulaExpre Top) `shouldBe` "⊤"

    it "revNeg: reverse the negation of a given formula" $ do
        revNeg (Neg (Var 'p')) `shouldBe` Var 'p'
        revNeg (Var 'p') `shouldBe` Neg (Var 'p')

    it "clausesPrint: print out the given clauses sets" $ do
        show (clausesPrint []) `shouldBe` ""
        show (clausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q']]) `shouldBe` "{ (¬ r) , (¬ p) , q }"
        show (clausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),
            Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),
            Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]) `shouldBe`
            "{ (¬ r) , (¬ p) , q },  { s , (¬ t) , (¬ p) },  { s , p , r },  { t , s , q },  { (¬ r) , (¬ p) , (¬ q) },  { s , t , r },  { p }"

    it "literalPrint: print out the given literals" $ do
        show (literalPrint []) `shouldBe` "[]"
        show (literalPrint [Neg (Var 'r'),Neg (Var 'p'),Var 'q']) `shouldBe` "(¬ r) , (¬ p) , q"
        show (literalPrint [Neg (Var 'r'),Neg (Var 'p'),Var 'q',Var 'r']) `shouldBe` "(¬ r) , (¬ p) , q , r"