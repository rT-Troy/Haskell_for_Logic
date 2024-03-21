import Test.Hspec

import CNF
import TruthTable
import PropResolution
import Common
import DPLL

main :: IO ()
main = hspec $ do
    describe "CNF" $ do
        it "step1: eliminate iff and implication from the input formula" $ do
            -- week6 lecture
            step1 ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe` (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r'))
            -- week7 exercise
            step1 ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :-> ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe` Neg (Var 'p' :\/ (Var 'q' :\/ Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')

        it "step2: push negations towards literals" $ do
            step2 (Neg (Var 'p' :\/ Var 'q') :\/ (Var 'q' :\/ Var 'r')) `shouldBe` (Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')
            step2 (Neg (Var 'p' :\/ (Var 'q' :\/ Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe` (Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')

        it "step3: distribute disjunctions into conjunctions" $ do
            step3 ((Neg (Var 'p') :/\ Neg (Var 'q')) :\/ (Var 'q' :\/ Var 'r')) `shouldBe` (Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))
            step3 ((Neg (Var 'p') :/\ (Neg (Var 'q') :/\ Neg (Var 'r'))) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe` (Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))

        it "cnfAlgo: convert a formula to CNF" $ do
            cnfAlgo ((Var 'p' :\/ Var 'q') :-> (Var 'q' :\/ Var 'r')) `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]
            cnfAlgo ((Var 'p' :\/ (Var 'q' :\/ Var 'r')) :-> ((Var 'p' :\/ Var 'q') :\/ Var 'r')) `shouldBe` [[Neg (Var 'q') :/\ Neg (Var 'r'),Var 'p',Var 'q',Var 'r']]
 
        it "step4delsub: remove duplicate variables" $ do
            step4delsub [[Var 'r'],[Neg (Var 'p'),Var 'q',Var 'r']] `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]

        it "step4: simplify resulting CNF-formulas by removing duplicate literals" $ do
            step4 ((Neg (Var 'p') :\/ (Var 'q' :\/ Var 'r')) :/\ (Neg (Var 'q') :\/ (Var 'q' :\/ Var 'r'))) `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r']]
            step4 ((Neg (Var 'p') :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r')) :/\ ((Neg (Var 'q') :/\ Neg (Var 'r')) :\/ ((Var 'p' :\/ Var 'q') :\/ Var 'r'))) `shouldBe` [[Neg (Var 'q') :/\ Neg (Var 'r'),Var 'p',Var 'q',Var 'r']]

        it "toClause: convert a CNF formula to a list of clauses" $ do
            toClause (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q'))) `shouldBe` [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')]

        it "eachClause: convert a list of clauses to a 2D list of literals" $ do
            eachClause [(Neg (Var 'p') :\/ Var 'q') :\/ Var 'r',Neg (Var 'p') :\/ Var 'r',Neg (Var 'q')] `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'p'),Var 'r'],[Neg (Var 'q')]]

        it "eachLiteral: convert a clause to a list of literals" $ do
            eachLiteral ((Neg (Var 'p') :\/ Var 'q') :\/ Var 'r') `shouldBe` [Neg (Var 'p'),Var 'q',Var 'r']

        it "toLiteral: convert a CNF formula to a 2D list of literals (non-repeating)" $ do
            toLiteral (((Neg (Var 'p')) :\/ Var 'q' :\/ Var 'r') :/\ ((Neg (Var 'p')) :\/ Var 'r') :/\ (Neg (Var 'q'))) `shouldBe` [[Neg (Var 'p'),Var 'q',Var 'r'],[Neg (Var 'p'),Var 'r'],[Neg (Var 'q')]]

        it "DPLL step1: eliminate iff and implication from the input formula" $ do
            -- week6 lecture
            step1 (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe` Neg (Neg (Var 'p' :/\ Var 'q') :\/ (Var 'q' :/\ Var 'r'))

        it "DPLL step2: push negations towards literals" $ do
            step2 (Neg (Neg (Var 'p' :/\ Var 'q') :\/ (Var 'q' :/\ Var 'r'))) `shouldBe` (Var 'p' :/\ Var 'q') :/\ (Neg (Var 'q') :\/ Neg (Var 'r'))

        it "DPLL toClause: convert a CNF formula to a list of clauses" $ do
            toClause ((Var 'p' :/\ Var 'q') :/\ (Neg (Var 'q') :\/ Neg (Var 'r'))) `shouldBe` [Var 'p',Var 'q',Neg (Var 'q') :\/ Neg (Var 'r')]


    describe "Common" $ do
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

    describe "TruthTable" $ do
        it "uniqVars: return all unique variables in a formula" $ do
            uniqVars ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r'))) `shouldBe` "pqr"

        it "allPosStatus: return all possible variable assignments" $ do
            allPosStatus "pq" `shouldBe` [[('p',T),('q',T)],[('p',T),('q',F)],[('p',F),('q',T)],[('p',F),('q',F)]]

        it "calculator: calculate the bool value of a given formula and case status" $ do
            calculator ((Var 'p' :-> (Var 'q' :-> Var 'r')) :-> ((Var 'p' :-> Var 'q') :-> (Var 'p' :-> Var 'r'))) [('p',T),('q',T),('r',T)] `shouldBe` T

    describe "PropResolution" $ do
        it "propResol: Implementing propositional resolution" $ do
            propResol [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r'] `shouldBe` [Var 'p',Var 'q',Neg (Var 's')]
        it "propResol: Implementing propositional resolution for empty clause" $ do
            propResol [Var 'p'] [Neg (Var 'p')] `shouldBe` []

    describe "DPLL" $ do
        it "calClause" $ do
            -- week 6 lecture
            calClause (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe` [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]