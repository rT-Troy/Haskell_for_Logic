module DPLLSpec where
import Test.Hspec
import Text.PrettyPrint
import Control.Exception

import Common
import DPLL

DPLLTests :: Spec
DPLLTests = describe "DPLL Tests" $ do
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