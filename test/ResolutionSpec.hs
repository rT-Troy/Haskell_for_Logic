module ResolutionSpec (resolutionTests) where
import Test.Hspec

import Common
import Resolution
import Text.PrettyPrint (render)

resolutionTests :: Spec
resolutionTests = describe "PropResolution Tests" $ do

    it "prFormulaPrint" $ do
        let formula = Neg ((Var 'p' :/\ Var 'q') :-> (Var 'q' :/\ Var 'r'))
        let expectedResult = unlines [
                "",
                "===Apply Resolution to a formula===",
                "",
                " The given formula is: ",
                " (¬ ((p ∧ q) → (q ∧ r))) ",
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
                " { p },  { q },  { (¬ q) , (¬ r) } ",
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
                " { p , q } { p , (¬ q) } { (¬ p) , q } { (¬ p) , (¬ q) } { p } { q },  { q , (¬ q) },  { p , (¬ p) },  { (¬ q) , q },  { p , (¬ p) },  { (¬ q) },  { p },  { p , (¬ q) },  { (¬ q) , p },  { (¬ p) },  { q },  { (¬ p) , q },  { q , (¬ p) },  { q , (¬ q) },  { (¬ p) , p },  { (¬ q) },  { (¬ p) },  { (¬ p) , (¬ q) },  { (¬ q) , (¬ p) },  { p },  { [] },  { q },  { (¬ q) } ",
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

    it "rmmFirst" $ do
        rmFirst (Var 'p') [] `shouldBe` []
