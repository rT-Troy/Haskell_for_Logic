module DPLLSpec (dpllTests) where
import Test.Hspec
import Text.PrettyPrint (render)


import Common
import DPLL
    ( dpllFormulaPrint,
      dpllClausesPrint,
      dpllFormula,
      dpllClauseSets,
      unitClause,
      eliminate,
      toCNFClauses,
      dpllResultPrint)

dpllTests :: Spec
dpllTests = describe "DPLL Tests" $ do

    -- it "dpllFormulaPrint" $ do
    --     let formula = (Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')
    --     let expectedResult = unlines [
    --             "",
    --             "===Applying DPLL algorithm to a CNF formula===",
    --             "",
    --             " The given formula is: ",
    --             " ((p ∧ q) → (q ∧ r)) ",
    --             "",
    --             " The negation is: ",
    --             " (¬ ((p ∧ q) → (q ∧ r))) ",
    --             "",
    --             " We want to show this formula is not valid, so its negation should be satisfiable... ",
    --             "",
    --             " ",
    --             "===Apply CNF algorithm to a formula===",
    --             "",
    --             " The given formula is:",
    --             " (¬ ((p ∧ q) → (q ∧ r))) ",
    --             "",
    --             "Step 1:",
    --             " (¬ ((¬ (p ∧ q)) ∨ (q ∧ r))) ",
    --             "",
    --             "Step 2:",
    --             " ((p ∧ q) ∧ ((¬ q) ∨ (¬ r))) ",
    --             "",
    --             "Step 3:",
    --             " ((p ∧ q) ∧ ((¬ q) ∨ (¬ r))) ",
    --             "",
    --             "Step 4, the clause set is:",
    --             " { { p },  { q },  { (¬ q) , (¬ r) } }",
    --             " ",
    --             " Applying DPLL algorithm to the clause set... ",
    --             "",
    --             "{ q },  { (¬ q) , (¬ r) }        Use unit  { p } ",
    --             "",
    --             "{ (¬ r) }        Use unit  { q } :",
    --             "",
    --             " The answer is: ",
    --             " { (¬ r) } ",
    --             "",
    --             " The result is: ",
    --             " It yields Ø, which is satisfiable. "
    --             ]
    --     render (dpllFormulaPrint formula) `shouldBe` expectedResult

    -- it "dpllClausesPrint" $ do
    --     let clauses = [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],[Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'],[Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],[Var 's',Var 't',Var 'r'],[Var 'p']]
    --     let expectedResult = unlines [
    --             "",
    --             "===Applying DPLL algorithm to clause sets===",
    --             "",
    --             " The clause set is: ",
    --             " { { (¬ r) , (¬ p) , q },  { s , (¬ t) , (¬ p) },  { s , p , r },  { t , s , q },  { (¬ r) , (¬ p) , (¬ q) },  { s , t , r },  { p } }",
    --             "",
    --             " Applying DPLL algorithm to the clause set...",
    --             "",
    --             " The answer is: ",
    --             " { [] } ",
    --             "",
    --             " The result is: ",
    --             " It yields empty clause □, which is unsatisfiable. "
    --             ]
    --     render (dpllClausesPrint clauses) `shouldBe` expectedResult


    it "toCNFClauses: " $ do
        -- week 6 lecture
        toCNFClauses (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
         [[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]]
        
 
    it "dpllFormula" $ do
        -- week 6 lecture
        dpllFormula (Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))) `shouldBe`
         [[Neg (Var 'r')]]

 
    it "dpllClauseSets" $ do
        -- week 7 exercise question 7.1.a
        dpllClauseSets [[Var 'p',Var 'q'],[Neg (Var 'p'),Var 'q'],
            [Var 'p',Neg (Var 'q')],[Neg (Var 'p'),Neg (Var 'q')]] `shouldBe` [[]]
        -- week 7 exercise question 7.1.b
        dpllClauseSets [[Neg (Var 'r'),Neg (Var 'p'),Var 'q'],[Var 's',Neg (Var 't'),Neg (Var 'p')],
         [Var 's',Var 'p', Var 'r'],[Var 't',Var 's', Var 'q'], [Neg (Var 'r'),Neg (Var 'p'),Neg (Var 'q')],
          [Var 's',Var 't',Var 'r'],[Var 'p']] `shouldBe` [[]]

    it "unitClause" $ do
        -- week 6 lecture
        unitClause (Var 'p')[[Var 'p'],[Var 'q'],[Neg (Var 'q'),Neg (Var 'r')]] `shouldBe` [[Neg (Var 'r')]]
        -- week 6 lecture
        unitClause (Neg (Var 'p')) [[Var 'p',Var 'q',Neg (Var 'r')],[Neg (Var 'p'),Var 'q',Neg (Var 'r')],
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
        eliminate (Neg (Var 'q')) [[Var 'q'],[Neg (Var 'q')]] `shouldBe` []

    it "dpllResultPrint" $ do 
        render (dpllResultPrint [[Neg (Var 'r')]]) `shouldBe` "It yields Ø, which is satisfiable."

        render (dpllResultPrint [[]]) `shouldBe` "It yields empty clause □, which is unsatisfiable."

