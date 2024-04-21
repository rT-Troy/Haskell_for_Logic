module ResolutionSpec (resolutionTests) where
import Test.Hspec

import Common
import Resolution

resolutionTests :: Spec
resolutionTests = describe "PropResolution Tests" $ do
    it "resolution: Implementing propositional resolution" $ do
        resolution [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r'] `shouldBe`
         [Var 'p',Var 'q',Neg (Var 's')]
    it "resolution: Implementing propositional resolution for empty clause" $ do
        resolution [Var 'p'] [Neg (Var 'p')] `shouldBe` []
    it "resoElim: Eliminating the tautological literals in a combined literal list of 2 clauses" $ do
        resoElim [Var 'p', Var 'q', Neg (Var 'r'), Neg (Var 's'), Var 'r'] `shouldBe`
         [Var 'p',Var 'q',Neg (Var 's')]