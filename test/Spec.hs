import Test.Hspec

import qualified CommonSpec
import qualified CNFSpec
import qualified ResolutionSpec
import qualified TruthTableSpec
import qualified DPLLSpec


main :: IO ()
main = hspec $ do
    CommonSpec.commonTests
    TruthTableSpec.truthTableTests
    CNFSpec.cnfTests
    ResolutionSpec.resolutionTests
    DPLLSpec.dpllTests
