module Jasmine.Alpha1.Header.TermNode.Test where

import Jasmine.Alpha1.Header.TermNode
import Jasmine.Alpha1.Header.TermNode.Util

getTermNodeUnit :: Int -> TermNode
getTermNodeUnit 0 = mkNLam (mkNApp (mkNLam (mkNIdx 0)) (mkNIdx 0))
getTermNodeUnit 1 = mkNLam (mkNApp (mkNLam (mkNApp (mkNIdx 0) (mkNIdx 0))) (mkNIdx 0))
getTermNodeUnit 2 = mkNLam (mkNLam (mkNApp (mkNLam (mkNApp (mkNIdx 0) (mkNIdx 2))) (mkNIdx 1)))
getTermNodeUnit _ = undefined

rewriteTest :: Int -> IO ()
rewriteTest = print . rewrite NF . getTermNodeUnit
