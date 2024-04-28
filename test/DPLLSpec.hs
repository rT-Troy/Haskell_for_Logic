{-# OPTIONS_GHC -Wno-unused-imports #-}
module DPLLSpec (dpllTests) where
import Test.Hspec
import Text.PrettyPrint (render)


import Common
import DPLL
    ( dpllFormulaPrint
    , dpllClausesPrint
    , dpllResultSets
    , dpllResultPrint
    , unitClausePrint
    , emptyPrint
    , checkNextSplit
    , dpllElimAll
    , dpllElim
    , toCNFClauses)
    
dpllTests :: Spec
dpllTests = describe "DPLL Tests" $ do

    it "dpllFormulaPrint" $ do
        let formula = (Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')
        let expectedResult = unlines [
                "",
                "===Applying DPLL algorithm to a formula===",
                "",
                " The given formula is: ",
                " ((p ∧ q) → (q ∧ r)) ",
                "",
                " The negation is: ",
                " (¬ ((p ∧ q) → (q ∧ r))) ",
                "",
                " If the formula is valid, so its negation should be un-satisfiable... ",
                " If the formula is not valid, so its negation should be satisfiable... ",
                "",
                " ",
                "===Apply CNF algorithm to a formula===",
                "",
                " The given formula is:",
                " (¬ ((p ∧ q) → (q ∧ r))) ",
                "",
                "Step 1:",
                " (¬ ((¬ (p ∧ q)) ∨ (q ∧ r))) ",
                "",
                "Step 2:",
                " ((p ∧ q) ∧ ((¬ q) ∨ (¬ r))) ",
                "",
                "Step 3:",
                " ((p ∧ q) ∧ ((¬ q) ∨ (¬ r))) ",
                "",
                "Step 4, the clause sets is:",
                " { { p },  { q },  { (¬ q) , (¬ r) } }",
                " ",
                "===Applying DPLL algorithm to clause sets===",
                "",
                " The clause set is: ",
                " { { p },  { q },  { (¬ q) , (¬ r) } } ",
                "",
                " { q },  { (¬ q) , (¬ r) }        Use unit  { p } ",
                "",
                " { (¬ r) }        Use unit  { q } ",
                "",
                "So the answer of this case is { Ø }. ",
                "",
                " The result is: ",
                " It yields Ø, which is satisfiable. "
                ]
        render (dpllFormulaPrint formula) `shouldBe` expectedResult

    it "dpllClausesPrint" $ do
        let clauses = [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
        let expectedResult = unlines [
                "",
                "===Applying DPLL algorithm to clause sets===",
                "",
                " The clause set is: ",
                " { { (¬ r) , (¬ p) , q },  { s , (¬ t) , (¬ p) },  { s , p , r },  { t , s , q },  { (¬ r) , (¬ p) , (¬ q) },  { s , t , r },  { p } } ",
                "",
                " { (¬ r) , q },  { s , (¬ t) },  { (¬ r) , (¬ q) },  { t , s , q },  { s , t , r }        Use unit  { p } ",
                "",
                "In case of  (¬ r)  -> 1: ",
                " { s , (¬ t) },  { s , t },  { t , s , q } ",
                "",
                "In case of  s  -> 1: ",
                " { [] } ",
                "",
                "So the answer of this case is { □ }. ",
                "",
                "In case of  s  -> 0: ",
                " { (¬ t) },  { t },  { t , q } ",
                "",
                " { q }        Use unit  { (¬ t) } ",
                "",
                "So the answer of this case is { Ø }. ",
                "",
                "In case of  (¬ r)  -> 0: ",
                " { q },  { (¬ q) },  { s , (¬ t) },  { t , s , q } ",
                "",
                " { s , (¬ t) }        Use unit  { q } ",
                "",
                "So the answer of this case is { Ø }. ",
                "",
                " The result is: ",
                " It exists empty clause □, which is unsatisfiable. "
                ]
        render (dpllClausesPrint clauses) `shouldBe` expectedResult


    it "toCNFClauses: " $ do
        -- week 6 lecture
        toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
         [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]



    it "dpllElimAll" $ do
        -- week 6 lecture
        dpllElimAll (Var 'p')[[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]] `shouldBe` [[Neg (Var 'r')]]
        -- week 6 lecture
        dpllElimAll (Neg (Var 'p')) [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],
         [Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']] `shouldBe` [[]]

    it "dpllElim: week 6 lecture" $ do
        -- week 6 lecture
        dpllElim (Neg (Var 'p')) [[Var 'p',Var 'q',Neg (Var 'r')],
         [Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'p',Var 'r']] `shouldBe`
         [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']]
        -- week 6 lecture
        dpllElim (Var 'r') [[Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Var 'r']] `shouldBe`
         [[Var 'q'],[Neg (Var 'q')]]
        -- week 6 lecture
        dpllElim (Neg (Var 'q')) [[Var 'q'],[Neg (Var 'q')]] `shouldBe` []


