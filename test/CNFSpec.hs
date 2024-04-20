module CNFSpec (cnfTests) where
import Test.Hspec
import Text.PrettyPrint (render)
import Control.Exception (evaluate)

import Common
import CNF

cnfTests :: Spec
cnfTests = describe "CNF Tests" $ do
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

    it "iffSplit" $ do
        iffSplit ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r')) `shouldBe` 
            ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) :/\
             ((Neg (Var 'q') :\/ (Var 'p' :\/ Var 'q')) :/\ (Neg (Var 'r') :\/ (Var 'p' :\/ Var 'q')))

    it "step1Each" $ do
        step1Each ((Top :\/ Var 'q') :-> (Var 'q' :\/ Bottom)) `shouldBe` 
            Neg (Top :\/ Var 'q') :\/ (Var 'q' :\/ Bottom)

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

        step2 ((Neg (Var 'p' :\/ Bottom) :\/ (Var 'q' :\/ Neg Top)) :/\ (Neg (Var 'q' :\/ Top) :\/ (Var 'p' :\/ Bottom))) `shouldBe`
            ((Neg (Var 'p') :/\ Top) :\/ (Var 'q' :\/ Bottom)) :/\ ((Neg (Var 'q') :/\ Bottom) :\/ (Var 'p' :\/ Bottom))

        evaluate (step2 (Var 'p' :-> Var 'q')) `shouldThrow`
            errorCall "There should have no -> notation, make sure the fomula has been processed by step1."

        evaluate (step2 (Var 'p' :<-> Var 'q')) `shouldThrow`
            errorCall "There should have no <-> notation, make sure the fomula has been processed by step1."

    it "step3: distribute disjunctions into conjunctions" $ do
        step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))

        step3 ((Var 'q' :\/ Var 'r') :\/ (Neg (Var 'p') :/\ Neg (Var 'q'))) `shouldBe`
            ((Var 'q' :\/ Var 'r') :\/ Neg (Var 'p')) :/\ ((Var 'q' :\/ Var 'r') :\/ Neg (Var 'q'))

        step3 ((Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
            (Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))

        step3 ((Neg (Var 'p') :\/ (Neg (Var 'q') :/\ Neg (Var 'r'))) :/\ ((Var 'p' :\/ Var 'q') :/\ Bottom :/\ Top)) `shouldBe`
            (Neg (Var 'p') :\/ (Neg (Var 'q') :/\ Neg (Var 'r'))) :/\ (((Var 'p' :\/ Var 'q') :/\ Bottom) :/\ Top)

        step3 (Top :\/ Bottom :\/ (Neg (Var 'p') :/\ Neg (Var 'q'))) `shouldBe` 
            ((Top :\/ Bottom) :\/ Neg (Var 'p')) :/\ ((Top :\/ Bottom) :\/ Neg (Var 'q'))

        evaluate (step3 (Var 'p' :-> Var 'q')) `shouldThrow`
            errorCall "There should have no -> notation, make sure the fomula has been processed by step1Each."

        evaluate (step3 (Var 'p' :<-> Var 'q')) `shouldThrow`
            errorCall "There should have no <-> notation, make sure the fomula has been processed by step1Each."

    it "cnfAlgo: convert a formula to CNF" $ do
        cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]

        cnfAlgo ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :-> ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
            [[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r']]

    it "step4delsub: remove duplicate variables" $ do
        step4delsub [[Var 'r'],[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']] `shouldBe`
         [[Neg (Var 'p'),Var 'q',Var 'r']]

        step4delsub [[Var 'd'],[Neg (Var 'p'),Var 'q',Var 'r']] `shouldBe`
         [[Var 'd'],[Neg (Var 'p'),Var 'q',Var 'r']]


    it "step4elim" $ do
        step4elim ([Neg (Var 'q'),Var 'q',Var 'r']) `shouldBe` [Var 'r']
        step4elim ([Neg (Var 'p'),Var 'q',Var 'r']) `shouldBe` [Neg (Var 'p'),Var 'q',Var 'r']

    it "step4: simplify resulting CNF-formulas by removing duplicate literals" $ do
        step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) `shouldBe`
            [[Neg (Var 'p'),Var 'q',Var 'r']]

        step4 ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\
            ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))) `shouldBe`
            [[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r']]

    it "DPLL step1: eliminate iff and implication from the input formula" $ do
        -- week6 lecture
        step1 (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
            Neg (Neg (Var 'p' :/\ Var 'q') :\/ (Var 'q' :/\ Var 'r'))

    it "DPLL step2: push negations towards literals" $ do
        step2 (Neg (Neg (Var 'p' :/\ Var 'q') :\/ (Var 'q' :/\ Var 'r'))) `shouldBe`
            (Var 'p' :/\ Var 'q') :/\ (Neg (Var 'q') :\/ Neg (Var 'r'))
