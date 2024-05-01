module ResolutionSpec (resolutionTests) where
import Test.Hspec

import Common
import Resolution
import Text.PrettyPrint (render)

resolutionTests :: Spec
resolutionTests = describe "PropResolution Tests" $ do

    it "prFormulaPrint" $ do
        let formula = (Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r')
        let expectedResult = unlines [
                "",
                "===Apply Resolution to a formula===",
                "",
                " The given formula is: ",
                " ((p ∧ q) → (q ∧ r)) ",
                "",
                " The negation is: ",
                " (¬ ((p ∧ q) → (q ∧ r))) ",
                "",
                " If the formula is valid, so its negation should be un-satisfiable... ",
                "  If the formula is not valid, so its negation should be satisfiable... ",
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
                "Step 4, the clause set is:",
                " { { p },  { q },  { (¬ q) , (¬ r) } }",
                " ",
                "===Applying Resolution to a clause set=== ",
                "",
                " The resolution clause set is: ",
                " { p } { q } { (¬ q) , (¬ r) } { p , q } { p , (¬ q) , (¬ r) } { (¬ r) },  { p , (¬ r) },  { (¬ r) , p },  { (¬ q) , (¬ r) },  { (¬ q) , p , (¬ r) },  { p , q , (¬ r) },  { q , p , (¬ r) },  { q , (¬ r) , p },  { p , (¬ q) , (¬ r) },  { (¬ q) , (¬ r) , p } ",
                "",
                " It yields Ø, which is satisfiable."
                ]
        render (prFormulaPrint formula) `shouldBe` expectedResult

    it "prClausesPrint" $ do
        -- week 6 lecture
        let clauses = [[Var 'p',Var 'q'],[Var 'p',Neg(Var 'q')],[Neg(Var 'p'),Var 'q'],[Neg(Var 'p'),Neg(Var 'q')]]
        let expectedResult = unlines [
                "",
                "===Applying Resolution to a clause set=== ",
                "",
                " The resolution clause set is: ",
                " { p , q } { p , (¬ q) },  { (¬ p) , q },  { (¬ p) , (¬ q) },  { p },  { q },  { [] } ",
                "",
                " It yields empty clause □, which is unsatisfiable."
                ]
        render (prClausesPrint clauses) `shouldBe` expectedResult


    it "prFinalClauses" $ do
        prFinalClauses [] `shouldBe` []


    it "prFinalClausesPrint" $ do
        render (prFinalClausesPrint []) `shouldBe` ""


    it "prValidChecker" $ do
        prValidChecker [[Neg (Var 'p')],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r'],
         [Var 'q',Var 'r'],[Var 'p',Var 'r'],[Var 'r'],[Var 'p',Var 'q'],[Var 'q'],[Var 'p'],[]] `shouldBe` True

        prValidChecker [[Neg (Var 'p')],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r'],
         [Var 'q',Var 'r'],[Var 'p',Var 'r'],[Var 'r'],[Var 'p',Var 'q'],[Var 'q'],[Var 'p']] `shouldBe` False

    
