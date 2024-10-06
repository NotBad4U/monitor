module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.SmallCheck as SC

import Data.Machine.Process
import Data.Machine.Type
import Data.Machine.Source

import Data.Map (Map(..), empty, fromList, singleton)


import Lib
    ( FLTL(..),
      simplfy,
      fltlMealy, Truth(..), δ4, mealy )

closedOpenFile = Prop 'e' `R` (Not (Prop 'o') :\/ ( Not (Prop 'e') `U` Prop 'c'))


main = defaultMain tests

tests :: TestTree
tests = testGroup "Testing Examples" [simplifyTests, mealyTests]

simplifyTests :: TestTree
simplifyTests = testGroup "simplify"
    [ 
        testCase "SimplifyGrp" $
            simplfy (TTrue :/\ Prop 'x') @?= Prop 'x'
        , testCase "simplfy2" $
            simplfy (FFalse :/\ Prop 'x') @?= FFalse
        , testCase "simplfy3s" $
            simplfy (TTrue :/\ G (F (Prop 'x'))) @?= G (F (Prop 'x'))
        , testCase "simplfy4" $
            simplfy (G (F (Prop 'x'))) @?= G (F (Prop 'x'))
        , testCase "simplfy5" $
            simplfy ((FFalse :\/ G (Prop 'x')) :/\ G (F (Prop 'x'))) @?= G (Prop 'x') :/\ G (F (Prop 'x'))
    ]


example = G (Not (Prop 'p') :\/ X (G (Prop 'q')))

mealyTests :: TestTree
mealyTests = testGroup "mealy"
    [ 
        testCase "mealy1" $
            δ4 (example, 'q')  @?= (PTop, example)
        , testCase "mealy2" $
            δ4 (example, 'p')  @?= (PBot, G (Prop 'q') :/\ example)
        , testCase "mealy3" $
            δ4 (G (Prop 'q') :/\ example, 'p')  @?= (Bot, FFalse)
        , testCase "mealy4" $
            δ4 (G (Prop 'q') :/\ example, 'q')  @?= (PTop, G (Prop 'q') :/\ example)
        , testCase "mealy5" $
            δ4 (FFalse, 'p')  @?= (Bot, FFalse)
        , testCase "mealy6" $
            δ4 (FFalse, 'q')  @?= (Bot, FFalse)
        , testCase "mealy7" $
            run (auto (fltlMealy example) <~ source "qqq" )  @?= [(PTop, example), (PTop, example), (PTop, example)]
    ]
