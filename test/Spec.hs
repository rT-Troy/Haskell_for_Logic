import Test.Hspec
import Text.PrettyPrint
import Control.Exception

import CNF
import Common
import PropResolution
import DPLL
import TruthTable

main :: IO ()
main = hspec $ do
    describe "CNF" $ do
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

        it "revNeg: reverse the negation of a given formula" $ do
            revNeg (Neg (Var 'p')) `shouldBe` Var 'p'
            revNeg (Var 'p') `shouldBe` Neg (Var 'p')

        it "clausesPrint: print out the given clauses sets" $ do
            show (clausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q']]) `shouldBe` "{ (¬ r) , (¬ p) , q }"
            show (clausesPrint [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),
                Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),
                Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]) `shouldBe`
                "{ (¬ r) , (¬ p) , q },  { s , (¬ t) , (¬ p) },  { s , p , r },  { t , s , q },  { (¬ r) , (¬ p) , (¬ q) },  { s , t , r },  { p }"

        it "literalPrint: print out the given literals" $ do
            show (literalPrint [Neg (Var 'r'),Neg (Var 'p'),Var 'q']) `shouldBe` "(¬ r) , (¬ p) , q"
            show (literalPrint [Neg (Var 'r'),Neg (Var 'p'),Var 'q',Var 'r']) `shouldBe` "(¬ r) , (¬ p) , q , r"

    describe "truthTable" $ do
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

    describe "PropResolution" $ do
        it "propResol: Implementing propositional resolution" $ do
            propResol [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r'] `shouldBe`
             [Var 'p',Var 'q',Neg (Var 's')]
        it "propResol: Implementing propositional resolution for empty clause" $ do
            propResol [Var 'p'] [Neg (Var 'p')] `shouldBe` []
        it "propSolve: Eliminating the tautological literals in a combined literal list of 2 clauses" $ do
            propSolve [Var 'p', Var 'q', Neg (Var 'r'), Neg (Var 's'), Var 'r'] `shouldBe`
             [Var 'p',Var 'q',Neg (Var 's')]

    describe "DPLL" $ do
        it "toClauses: " $ do
            -- week 6 lecture
            toClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
             [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
        it "dpllFormula" $ do
            -- week 6 lecture
            dpllFormula (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')))
                `shouldBe` [[Neg (Var 'r')]]
        it "dpllClauseSets" $ do
            -- week 7 exercise question 7.1.a
            dpllClauseSets [[Var 'p',Var 'q'],[Neg (Var 'p'),Var 'q'],
             [Var 'p',Neg (Var 'q')],[Neg (Var 'p'),Neg (Var 'q')]] `shouldBe` [[]]
            -- week 7 exercise question 7.1.b
            dpllClauseSets [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],
             [Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
                `shouldBe` [[]]
        it "unitClause" $ do
            -- week 6 lecture
            unitClause [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]] `shouldBe` [[Neg (Var 'r')]]
        it "unitNegClause" $ do
            -- week 6 lecture
            unitNegClause [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],
             [Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']] `shouldBe` [[]]
        it "eliminate: week 6 lecture" $ do
            -- week 6 lecture
            eliminate (Neg (Var 'p')) [[Var 'p',Var 'q',Neg (Var 'r')],
             [Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'p',Var 'r']] `shouldBe`
              [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']]
            -- week 6 lecture
            eliminate (Var 'r') [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']] `shouldBe`
             [[Var 'q'],[Neg (Var 'q')]]
            -- week 6 lecture
            eliminate (Neg (Var 'q')) [[Var 'q'],[Neg (Var 'q')]] `shouldBe` [[]]

