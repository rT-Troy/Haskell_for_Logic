module PropResoSpec where
import Test.Hspec
import Text.PrettyPrint
import Control.Exception

import Common
import PropResolution

PropResolutionTests :: Spec
PropResolutionTests = describe "PropResolution Tests" $ do
    it "propResol: Implementing propositional resolution" $ do
        propResol [Var 'p', Var 'q', Neg (Var 'r')] [Neg (Var 's'), Var 'r'] `shouldBe`
            [Var 'p',Var 'q',Neg (Var 's')]
    it "propResol: Implementing propositional resolution for empty clause" $ do
        propResol [Var 'p'] [Neg (Var 'p')] `shouldBe` []
    it "propSolve: Eliminating the tautological literals in a combined literal list of 2 clauses" $ do
        propSolve [Var 'p', Var 'q', Neg (Var 'r'), Neg (Var 's'), Var 'r'] `shouldBe`
            [Var 'p',Var 'q',Neg (Var 's')]