module ResolutionSpec (resolutionTests) where
import Test.Hspec

import Common
import Resolution

resolutionTests :: Spec
resolutionTests = describe "PropResolution Tests" $ do


    it "prValidChecker" $ do
        prValidChecker [[Neg (Var 'p')],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r'],
         [Var 'q',Var 'r'],[Var 'p',Var 'r'],[Var 'r'],[Var 'p',Var 'q'],[Var 'q'],[Var 'p'],[]] `shouldBe` True

        prValidChecker [[Neg (Var 'p')],[Neg (Var 'q')],[Neg (Var 'r')],[Var 'p',Var 'q',Var 'r'],
         [Var 'q',Var 'r'],[Var 'p',Var 'r'],[Var 'r'],[Var 'p',Var 'q'],[Var 'q'],[Var 'p']] `shouldBe` False

    
