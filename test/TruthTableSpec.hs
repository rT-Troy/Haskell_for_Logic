module TruthTableSpec (truthTableTests) where
import Test.Hspec
import Text.PrettyPrint (render)
import Control.Exception (evaluate)

import Common
import TruthTable

truthTableTests :: Spec
truthTableTests = describe "TruthTable Tests" $ do
    it "truthTable: generate a pretty truth table of a given formula" $ do
        let formula = (Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r'))
        let expectedResult = unlines [
                "The given formula is:\n ((p → (q → r)) → ((p → q) → (p → r))) \nTruth table result:\n p\tq\tr\tResult\nT\tT\tT\tT\nT\tT\tF\tT\nT\tF\tT\tT\nT\tF\tF\tT\nF\tT\tT\tT\nF\tT\tF\tT\nF\tF\tT\tT\nF\tF\tF\tT "
                ]
        render (truthTablePrint formula) `shouldBe` expectedResult

    it "uniqVars: return all unique variables in a formula" $ do
        uniqVars ((Var 'p' :\/ Var 'd') :-> (Var 'q' :/\ Var 'r')) `shouldBe` "pdqr"
        uniqVars ((Var 'p' :\/ Neg (Var 'd') :\/ Bottom) :<-> (Var 'q' :/\ Var 'r' :/\ Top)) `shouldBe` "pdqr"

    it "allPosStatus: return all possible variable assignments" $ do
        allPosStatus "pq" `shouldBe` [[('p',T),('q',T)],[('p',T),('q',F)],[('p',F),('q',T)],[('p',F),('q',F)]]

    it "calculator: calculate the bool value of a given formula and case status" $ do
        calculator ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q')
            :-> (Var 'p' :-> Var 'r'))) [('p',T),('q',T),('r',T)] `shouldBe` T
        calculator ((Neg (Var 'p') :\/ Neg (Var 'd') :\/ Bottom)
            :-> (Var 'q' :/\ Var 'r' :/\ Top)) [('p',T),('d',F),('q',T),('r',F)] `shouldBe` F
        calculator (Var 'p' :/\ Var 'q') [('p',T),('q',F)] `shouldBe` F
        calculator (Var 'p' :/\ Var 'q') [('p',T),('q',T)] `shouldBe` T
        calculator (Var 'p' :\/ Var 'q') [('p',T),('q',F)] `shouldBe` T
        calculator (Var 'p' :\/ Var 'q') [('p',F),('q',F)] `shouldBe` F
        evaluate (calculator (Var 'p' :<-> Var 'q') [('p',T),('q',T)]) `shouldThrow` errorCall "The formula is invalid."
        evaluate (calculator (Var 'p' :-> Var 'q') [('p',T)]) `shouldThrow` errorCall "Variable 'q' not found in status."
        calculator Bottom [] `shouldBe` F
        calculator Top [] `shouldBe` T