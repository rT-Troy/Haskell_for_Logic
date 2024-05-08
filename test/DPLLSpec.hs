{-# OPTIONS_GHC -Wno-unused-imports #-}
module DPLLSpec (dpllTests) where
import Test.Hspec
import Text.PrettyPrint (render)


import Common
import DPLL
    ( dpllFormulaPrint
    , dpllClausesPrint
    , dpllClauses
    , dpllResultPrint
    , dpllResultPrint
    , eachClausePrint
    , eachClause
    , emptyPrint
    , dpllCheckNextSplit
    , dpllElimAll
    , dpllElim
    , dpllResultSatisfy
    , toCNFClauses, unitClause)
    
dpllTests :: Spec
dpllTests = describe "DPLL Tests" $ do

    it "dpllFormulaPrint" $ do
        let formula = Var 'p' :/\ Var 'q'
        let expectedResult = unlines [
                "",
                "===Applying DPLL algorithm to a formula===",
                "",
                " The given formula is: ",
                " (p ∧ q) ",
                "===Apply CNF algorithm to a formula===",
                "",
                " The given formula is:",
                " (p ∧ q) ",
                "",
                "Step 1:",
                " (p ∧ q) ",
                "",
                "Step 2:",
                " (p ∧ q) ",
                "",
                "Step 3:",
                " (p ∧ q) ",
                "",
                "Step 4, the clause set is:",
                " { { p },  { q } }",
                " ",
                "===Applying DPLL algorithm to a clause set===",
                "",
                " The clause set is: ",
                " { { p },  { q } } ",
                "",
                " { q }        Use unit { p } ",
                "",
                "So the answer of this case is { Ø }.  ",
                "",
                " The result is: ",
                " It exists Ø, which is satisfiable. "
                ]
        render (dpllFormulaPrint formula) `shouldBe` expectedResult

    it "dpllClausesPrint" $ do
        let clauses = [[Var 'p'],[Var 'q',Neg (Var 'p')]]
        let expectedResult = unlines [
                    "",
                    "===Applying DPLL algorithm to a clause set===",
                    "",
                    " The clause set is: ",
                    " { { p },  { q , (¬ p) } } ",
                    "",
                    " { q }        Use unit { p }  ",
                    "",
                    " The result is: ",
                    " It exists Ø, which is satisfiable. "
                ]
        render (dpllClausesPrint clauses) `shouldBe` expectedResult


    it "dpllResultPrint" $ do
        render (dpllResultPrint [F,F,F]) `shouldBe` "All path yields empty clause □, which is unsatisfiable."

    it "dpllClauses" $ do
        dpllClauses [[Var 'p',Var 'q',Neg(Var 'r')],[Neg(Var 'p'),Var 'q',Neg(Var 'r')],[Neg(Var 'q'),Neg(Var 'r')],[Neg(Var 'p'),Var 'r'],[Var 'p',Var 'r']]
         [Var 'p',Var 'q',Var 'r'] `shouldBe` [F,F]

    it "eachClausePrint" $ do
        render (eachClausePrint [] (Var 'p')) `shouldBe` "\n\nSo the answer of this case is { □ }."
        render (eachClausePrint [[Var 'p',Var 'q'],[Var 'q', Var 'p']] (Var 'p')) `shouldBe` "\n\nIn case of { p } -> 1: \n { [] } \n\nIn case of { p } -> 0: \n { q },  { q } \n\n { [] }        Use unit { q }"


    it "toCNFClauses: " $ do
        -- week 6 lecture
        toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
         [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]


    it "dpllCheckNextSplit" $ do
        dpllCheckNextSplit [[Var 'p'], [Neg (Var 'p')], [Var 'r']] `shouldBe` True


    it "checkNextSplit" $ do
        dpllElimAll (Neg (Var 'p')) [[Var 'p'], [Neg (Var 'p')]] `shouldBe` [[]]


    it "dpllElimAll" $ do
        -- week 6 lecture
        dpllElimAll (Var 'p')[[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]] `shouldBe` [[Neg (Var 'r')]]
        -- week 6 lecture
        dpllElimAll (Neg (Var 'p')) [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],
         [Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p',Var 'r']] `shouldBe` [[]]


    it "dpllResultSatisfy" $ do
        dpllResultSatisfy [F,F,F] `shouldBe` False
        dpllResultSatisfy [T,T] `shouldBe` True

    it "unitClause" $ do
        unitClause [[]] `shouldBe` Nothing
        unitClause [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')]] `shouldBe` Just [Var 'p',Var 'q',Var 'r']

    it "emptyPrint" $ do
        render (emptyPrint []) `shouldBe` "{ [] }"


    it "eachClause" $ do
        -- week 6 lecture
        eachClause [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],[Neg (Var 'q'),Neg (Var 'r')],[Neg (Var 'p'),Var 'r'],[Var 'p']] (Var 'p') `shouldBe` []
        eachClause [] (Var 'p') `shouldBe` [F]

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


