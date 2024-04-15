import Test.Hspec

import qualified CommonSpec
import qualified CNFSpec
import qualified PropResoSpec
import qualified TruthTableSpec
import qualified DPLLSpec


main :: IO ()
main = hspec $ do
    CommonSpec.commonTests
    TruthTableSpec.truthTableTests
    CNFSpec.cnfTests
    PropResoSpec.propResolutionTests
    DPLLSpec.dpllTests
