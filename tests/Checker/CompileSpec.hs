module Syntax.CompileSpec where

import Test.HSpec hiding (Spec)
import qualified Test.HSpec as Test

instance Arbitrary

spec :: Test.Spec
spec = do
  describe "compiling tests" $
    it "compilation of + is associative" $
        property $ (\c1 c2 c3 k vars -> compile (CPlus c1 (CPlus c2 c3)) k vars
                                     == compile (CPlus (CPlus c1 c2) c3) k vars)
    