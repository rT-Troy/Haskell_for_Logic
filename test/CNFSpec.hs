module CNFSpec (cnfTests) where
import Test.Hspec
import Text.PrettyPrint (render)
import Control.Exception (evaluate)

import Common
import CNF

cnfTests :: Spec
cnfTests = describe "CNF Tests" $ do
    -- week6 lecture
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
                "Step 4, the clause sets is:",
                " { { (¬ p) , q , r } }"
                ]
        render (cnfPrint formula) `shouldBe` expectedResult


    it "cnfAlgo: convert a formula to CNF" $ do
        -- week6 lecture
        cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]
        -- not sure if this is correct
        cnfAlgo (Neg ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r'))) `shouldBe` [[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q']]
        -- ((p → q) ↔ (q → p))    The answer shows (Q ∨ ¬P) ∧ (P ∨ ¬Q) is also correct.
        cnfAlgo ((Var 'p' :-> Var 'q') :<-> (Var 'q' :-> Var 'p')) `shouldBe` [[Neg (Var 'q'),Var 'p']]
        -- (¬ (p → q))
        cnfAlgo (Neg (Var 'p' :-> Var 'q')) `shouldBe` [[Var 'p'],[Neg (Var 'q')]]
        -- (⊤ → q) ≡ ((p ∧ (¬ p)) → q)
        cnfAlgo (Bottom :-> Var 'q') `shouldBe` [[Top]]
        -- (p → ((q → r) → ((¬ s) ∨ r)))
        cnfAlgo (Var 'p' :-> ((Var 'q' :-> Var 'r') :/\ ((Neg (Var 's')) :\/ Var 'r'))) `shouldBe` 
         [[Neg (Var 'p'),Neg (Var 'q'),Var 'r'],[Neg (Var 'p'),Neg (Var 's'),Var 'r']]
        -- ((p → q) ∨ (q → p))
        cnfAlgo ((Var 'p' :-> Var 'q') :\/ (Var 'q' :-> Var 'p')) `shouldBe` [[Top]]
        -- ((¬ (¬ (¬ p))) → (¬ ((q ∧ (¬ r)) ∨ ((¬ q) → r))))
        -- This answer has been simplified.
        cnfAlgo ((Neg(Neg(Neg (Var 'p')))) :-> Neg ((Var 'q' :/\ Neg (Var 'r')) :\/ (Neg (Var 'q') :-> Var 'r'))) `shouldBe`
         [[Var 'p',Neg (Var 'r')],[Var 'p',Neg (Var 'q'),Var 'r']]
        -- ((p ∧ (¬ p)) → q)
        cnfAlgo ((Var 'p' :/\ Neg (Var 'p')) :-> Var 'q') `shouldBe` [[Top]]
        -- ((p → r) ↔ (q → p))      answer is not [[Neg (Var 'r'),Neg (Var 'q'),Var 'p'],[Var 'q',Neg (Var 'p'),Var 'r']]
        cnfAlgo ((Var 'p' :-> Var 'r') :<-> (Var 'q' :-> Var 'p')) `shouldBe` [[Var 'p',Neg (Var 'q')],[Neg (Var 'p'),Var 'r']]
        -- (p → (q ∧ (¬ q)))    The answer shows (Q ∨ ¬P) ∧ (¬Q ∨ ¬P), is also correct.
        cnfAlgo (Var 'p' :-> (Var 'q' :/\ Neg (Var 'q'))) `shouldBe` [[Neg (Var 'p')]]


    it "step1: eliminate iff and implication from the input formula" $ do
        -- week6 lecture
        step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe`
         Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')
        -- week7 Exercise Question 7.2
        step1 ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :-> ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
         Neg (Var 'p' :\/ (Var 'q' :\/ Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')
        -- (((p ∨ q) ↔ q) ∨ r)
        step1 ((Var 'p' :\/ Var 'q') :<-> (Var 'q' :\/ Var 'r')) `shouldBe`
         (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q'))


    it "step2: push negations towards literals" $ do
    --     step2 (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) `shouldBe`
    --      (Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')
        -- week7 Exercise Question 7.2
        step2 (Neg (Var 'p' :\/ (Var 'q' :\/ Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
         (Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')
        -- (¬ (p ∧ (¬ p)))
        step2 (Neg (Var 'p' :/\ Neg (Var 'p'))) `shouldBe` Top
    --     -- (((p ∨ q) ↔ q) ∨ r)
    --     step2 ((Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q' :\/ Var 'r') :\/ (Var 'p' :\/ Var 'q'))) `shouldBe`
    --      ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))

    --     step2 ((Neg (Var 'p' :\/ Bottom) :\/ (Var 'q' :\/ Neg Top)) :/\ (Neg (Var 'q' :\/ Top) :\/ (Var 'p' :\/ Bottom))) `shouldBe`
    --      ((Neg (Var 'p') :/\ Top) :\/ (Var 'q' :\/ Bottom)) :/\ ((Neg (Var 'q') :/\ Bottom) :\/ (Var 'p' :\/ Bottom))

    --     evaluate (step2 (Var 'p' :-> Var 'q')) `shouldThrow`
    --      errorCall "There should have no -> notation, make sure the fomula has been processed by step1."

    --     evaluate (step2 (Var 'p' :<-> Var 'q')) `shouldThrow`
    --      errorCall "There should have no <-> notation, make sure the fomula has been processed by step1."

    -- it "step3: distribute disjunctions into conjunctions" $ do
    --     step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) `shouldBe`
    --      (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))

    --     step3 ((Var 'q' :\/ Var 'r') :\/ (Neg (Var 'p') :/\ Neg (Var 'q'))) `shouldBe`
    --      ((Var 'q' :\/ Var 'r') :\/ Neg (Var 'p')) :/\ ((Var 'q' :\/ Var 'r') :\/ Neg (Var 'q'))
    --     -- week7 Exercise Question 7.2
    --     step3 ((Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe`
    --      (Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ (Neg (Var 'r') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')))

    --     step3 ((Neg (Var 'p') :\/ (Neg (Var 'q') :/\ Neg (Var 'r'))) :/\ ((Var 'p' :\/ Var 'q') :/\ Bottom :/\ Top)) `shouldBe`
    --      (Neg (Var 'p') :\/ (Neg (Var 'q') :/\ Neg (Var 'r'))) :/\ (((Var 'p' :\/ Var 'q') :/\ Bottom) :/\ Top)

    --     step3 (Top :\/ Bottom :\/ (Neg (Var 'p') :/\ Neg (Var 'q'))) `shouldBe` 
    --      ((Top :\/ Bottom) :\/ Neg (Var 'p')) :/\ ((Top :\/ Bottom) :\/ Neg (Var 'q'))

    --     evaluate (step3 (Var 'p' :-> Var 'q')) `shouldThrow`
    --      errorCall "There should have no -> notation, make sure the fomula has been processed by step1imp."

    --     evaluate (step3 (Var 'p' :<-> Var 'q')) `shouldThrow`
    --      errorCall "There should have no <-> notation, make sure the fomula has been processed by step1imp."



    -- it "step4delsub: remove duplicate variables" $ do
    --     step4delsub [[Var 'r'],[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']] `shouldBe`
    --      [[Neg (Var 'p'),Var 'q',Var 'r']]

    --     step4delsub [[Var 'd'],[Neg (Var 'p'),Var 'q',Var 'r']] `shouldBe`
    --      [[Var 'd'],[Neg (Var 'p'),Var 'q',Var 'r']]


    -- it "step4elim" $ do
    --     step4elim [Neg (Var 'q'),Var 'q',Var 'r'] `shouldBe` [Var 'r']

    --     step4elim [Neg (Var 'p'),Var 'q',Var 'r'] `shouldBe` [Neg (Var 'p'),Var 'q',Var 'r']


    -- it "step4: simplify resulting CNF-formulas by removing duplicate literals" $ do
    --     step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) `shouldBe`
    --      [[Neg (Var 'p'),Var 'q',Var 'r']]
    --     -- week7 Exercise Question 7.2
    --     step4 ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\
    --      ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))) `shouldBe`
    --      [[Neg (Var 'q')],[Var 'q',Var 'r'],[Var 'p',Var 'q']]

    --     step4 (((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ (Var 'p' :\/ Var 'q'))) `shouldBe`
    --      [[Neg (Var 'p')],[Neg (Var 'q')],[Var 'r'],[Neg (Var 'r'),Var 'p',Var 'q']]
    --     -- step4 (((Var 'p' :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ (Var 'q' :/\ (Neg (Var 'q') :/\ Neg (Var 'r')))) :/\ ((Var 'q' :/\ (Neg (Var 'p') :/\ Neg (Var 'q'))) :\/ (Var 'r' :/\ (Neg (Var 'p') :/\ Neg (Var 'q'))))) `shouldBe`
         
    -- it "toClauseSets" $ do
    --     toClauseSets ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\
    --      ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))) `shouldBe` 
    --      [[Neg (Var 'p'),Var 'p',Var 'q',Var 'r'],[Neg (Var 'q')],[Neg (Var 'r'),Var 'p',Var 'q',Var 'r']]
    --     -- week7 Exercise Question 7.2
    --     toClauseSets ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :/\ ((Neg (Var 'p') :/\ Neg (Var 'q')) :/\ Neg (Var 'r'))) `shouldBe`
    --      [[Var 'p',Var 'q',Var 'r'],[Neg (Var 'p')],[Neg (Var 'q')],[Neg (Var 'r')]]

    -- it "stringFilter" $ do
    --     stringFilter ((Top :-> Var 'q') :<-> (Var 'q' :\/ Bottom)) `shouldBe` 
    --      "Top :-> Var 'q' :<-> Var 'q' :\\/ Bottom"

    -- it "strToLogicFormula" $ do
    --     strToLogicFormula "Var 'p'" `shouldBe` Var 'p'
    --     strToLogicFormula "Neg (Var 'p')" `shouldBe` Neg (Var 'p')
    --     strToLogicFormula "Neg (Var 'p') :/\\ Top" `shouldBe` (Neg (Var 'p') :/\ Top)
    --     strToLogicFormula (show (Var 'p')) `shouldBe` Var 'p'