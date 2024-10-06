{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Algebra.Lattice
import qualified Data.GraphViz as G
import qualified Data.GraphViz.Attributes.Complete as G
import qualified Data.GraphViz.Types as G
import Data.List (nub)
import Data.Map (Map (..), difference, empty, fromList, singleton, toList)
import qualified Data.Rewriting.Problem as TL
import Data.Rewriting.Rules as Rules
import Data.Rewriting.Term (Term (..))
import qualified Data.Rewriting.Term as Term
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import Lib

showTrm :: Term OperatorTerm Char -> String
showTrm = show

closedOpenFile :: FLTL
closedOpenFile = Prop 'e' `R` (Not (Prop 'o') :\/ (Not (Prop 'e') `U` Prop 'c'))

example = G (Not (Prop 'p') :\/ X (G (Prop 'q')))

labelEdge :: (Char, Truth) -> TL.Text
labelEdge (letter, emit) = TL.singleton letter <> TL.singleton '/' <> TL.pack (show emit)

mealyGraphParams :: G.GraphvizParams String String (Char, Truth) () String
mealyGraphParams =
  G.defaultParams
    { G.fmtNode = \(v, vl) -> colorAttribute $ G.RGB 0 0 0,
      G.fmtEdge = \(from, to, el) -> G.textLabel (labelEdge el) : colorAttribute (G.RGB 40 255 40)
    }
  where
    colorAttribute color = [G.Color $ G.toColorList [color]]

main :: IO ()
main =
  let transitions = mealy example empty ['p', 'q']
   in let (nodes, edges) = unzip $ (\((src, letter), (emit, tgt)) -> ((show src, show src), (show src, show tgt, (letter, emit)))) <$> toList transitions
       in let dotGraph = G.graphElemsToDot mealyGraphParams (nub nodes) edges
           in let dotText = G.printDotGraph dotGraph
               in TL.writeFile "files.dot" dotText