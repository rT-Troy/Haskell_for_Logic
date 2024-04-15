module CNFSpec where
import Test.Hspec
import Text.PrettyPrint
import Control.Exception

import Common
import CNF

CNFTests :: Spec
CNFTests = describe "CNF Tests" $ do
    it "cnfPrint: convert a formula to CNF" $ do
        let formula = (Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')
        let expectedResult = unlines [
                "",
                "===Apply CNF algorithm to a formula===",
                "",
                " The given formula is:",
                " ((p ∨ q) → (q ∨ r)) ",
                "",
                "Step 1:",
                " ((¬ (p ∨ q)) ∨ (q ∨ r)) ",
                "",
                "Step 2:",
                " (((¬ p) ∧ (¬ q)) ∨ (q ∨ r)) ",
                "",
                "Step 3:",
                " (((¬ p) ∨ (q ∨ r)) ∧ ((¬ q) ∨ (q ∨ r))) ",
                "",
                "Step 4, the clause set is:",
                " { { (¬ p) , q , r } }"
                ]
        render (cnfPrint formula) `shouldBe` expectedResult

    it "step1: eliminate iff and implication from the input formula" $ do
        -- week6 lecture
        step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r'))
        -- week7 exercise
        step1 ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :-> ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
            Neg (Var 'p' :\/ (Var 'q' :\/ Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')

        step1 ((Var 'p' :\/ Bottom) :<-> (Var 'q' :\/ Top)) `shouldBe`
            (Neg (Var 'p' :\/ Bottom) :\/ (Var 'q' :\/ Top)) :/\ (Neg (Var 'q' :\/ Top) :\/ (Var 'p' :\/ Bottom))


    it "step2: push negations towards literals" $ do
        step2 (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')
        
        step2 (Neg (Var 'p' :\/ (Var 'q' :\/ Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')

        step2 (Neg (Var 'p' :\/ Bottom) :\/ (Var 'q' :\/ Neg Top)) :/\ (Neg (Var 'q' :\/ Top) :\/ (Var 'p' :\/ Bottom)) `shouldBe`
            ((Neg (Var 'p') :/\ Top) :\/ (Var 'q' :\/ Bottom)) :/\ (Neg (Var 'q' :\/ Top) :\/ (Var 'p' :\/ Bottom))

        evaluate (step2 (Var 'p' :-> Var 'q')) `shouldThrow`
            errorCall "There should have no -> notation, make sure the fomula has been processed by step1."

        evaluate (step2 (Var 'p' :<-> Var 'q')) `shouldThrow`
            errorCall "There should have no <-> notation, make sure the fomula has been processed by step1."

    it "step3: distribute disjunctions into conjunctions" $ do
        step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))

        step3 ((Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))

        step3 ((Neg (Var 'p') :\/ (Neg (Var 'q') :/\ Neg (Var 'r'))) :/\ ((Var 'p' :\/ Var 'q') :/\ Bottom :/\ Top)) `shouldBe`
            ((Neg (Var 'p') :\/ Neg (Var 'q')) :/\ (Neg (Var 'p') :\/ Neg (Var 'r'))) :/\ (((Var 'p' :\/ Var 'q') :/\ Bottom) :/\ Top)

        evaluate (step3 (Var 'p' :-> Var 'q')) `shouldThrow`
            errorCall "There should have no -> notation, make sure the fomula has been processed by step1."

        evaluate (step3 (Var 'p' :<-> Var 'q')) `shouldThrow`
            errorCall "There should have no <-> notation, make sure the fomula has been processed by step1."

    it "cnfAlgo: convert a formula to CNF" $ do
        cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]

        cnfAlgo ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :-> ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
            [[Neg (Var 'q') :/\ Neg (Var 'r'),Var 'p',Var 'q',Var 'r']]

    it "step4delsub: remove duplicate variables" $ do
        step4delsub [[Var 'r'],[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']] `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]

    it "step4elim" $ do
        step4elim ([Neg (Var 'q'),Var 'q',Var 'r']) `shouldBe` [Var 'r']

    it "step4: simplify resulting CNF-formulas by removing duplicate literals" $ do
        step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) `shouldBe`
            [[Neg (Var 'p'),Var 'q',Var 'r']]

        step4 ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\
            ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))) `shouldBe`
            [[Neg (Var 'q') :/\ Neg (Var 'r'),Var 'p',Var 'q',Var 'r']]

    it "toClause: convert a CNF formula to a list of clauses" $ do
        toClause (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q'))) `shouldBe` 
            [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')]

    it "eachClause: convert a list of clauses to a 2D list of literals" $ do
        eachClause [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')] `shouldBe`
            [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'p'),Var 'r'],[Neg (Var 'q')]]

    it "eachLiteral: convert a clause to a list of literals" $ do
        eachLiteral ((Neg (Var 'p') :\/ Var 'q') :\/ Var 'r') `shouldBe`
            [Neg (Var 'p'),Var 'q',Var 'r']

    it "toLiteral: convert a CNF formula to a 2D list of literals (non-repeating)" $ do
        toLiteral (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\
            ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q'))) `shouldBe`
            [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'p'),Var 'r'],[Neg (Var 'q')]]

    it "DPLL step1: eliminate iff and implication from the input formula" $ do
        -- week6 lecture
        step1 (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
            Neg (Neg (Var 'p' :/\ Var 'q') :\/ (Var 'q' :/\ Var 'r'))

    it "DPLL step2: push negations towards literals" $ do
        step2 (Neg (Neg (Var 'p' :/\ Var 'q') :\/ (Var 'q' :/\ Var 'r'))) `shouldBe`
            (Var 'p' :/\ Var 'q') :/\ (Neg (Var 'q') :\/ Neg (Var 'r'))

    it "DPLL toClause: convert a CNF formula to a list of clauses" $ do
        toClause ((Var 'p' :/\ Var 'q') :/\ (Neg (Var 'q') :\/ Neg (Var 'r'))) `shouldBe`
            [Var 'p',Var 'q',Neg (Var 'q') :\/ Neg (Var 'r')]