import Test.Hspec
import Text.PrettyPrint
import Control.Exception

import CNF
import Common
import PropResolution
import DPLL
import TruthTable

import qualified CommonSpec
import qualified CNFSpec
import qualified PropResoSpec
import qualified TruthTableSpec
import qualified DPLLSpec


main :: IO ()
main = hspec $ do
    describe "CNF tests"  CNFSpec.CNFTests
    describe "PropResolution tests" PropResoSpec.PropResolutionTests
    describe "TruthTable tests" TruthTableSpec.truthTableTests
    describe "DPLL tests" DPLLSpec.DPLLTests
    describe "Common tests" CommonSpec.CommonTests