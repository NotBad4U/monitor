{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}

module Lib where

import Algebra.Lattice
import Data.List ((\\))
import Data.Machine.Mealy as Mealy
import Data.Machine.Process
import Data.Machine.Source
import Data.Machine.Type (run)
import Data.Map (Map (..), difference, elems, empty, fold, fromList, union)
import qualified Data.Rewriting.Context as Ctxt
import Data.Rewriting.Rule (Rule (..))
import Data.Rewriting.Rules as Rules
import Data.Rewriting.Term (Term (..))
import qualified Data.Rewriting.Term as Term
import Debug.Trace

data Truth = Top | PTop | PBot | Bot
  deriving (Eq)

instance Lattice Truth where
  Top \/ _ = Top
  _ \/ Top = Top
  Bot \/ a = a
  a \/ Bot = a
  PTop \/ PTop = PTop
  PTop \/ PBot = PTop
  PBot \/ PTop = PTop
  PBot \/ PBot = PBot

  Top /\ a = a
  a /\ Top = a
  Bot /\ _ = Bot
  _ /\ Bot = Bot
  PTop /\ PBot = PBot
  PBot /\ PTop = PBot
  PTop /\ PTop = PTop
  PBot /\ PBot = PBot

(⊓) :: Truth -> Truth -> Truth
p ⊓ q = p /\ q

(⊔) :: Truth -> Truth -> Truth
p ⊔ q = p \/ q

instance BoundedJoinSemiLattice Truth where
  bottom = Bot

instance BoundedMeetSemiLattice Truth where
  top = Top

instance Show Truth where
  show Top = "⊤"
  show PTop = "⊤p"
  show PBot = "⊥p"
  show Bot = "⊥"

data FLTL
  = TTrue
  | FFalse
  | Prop Char
  | FLTL :\/ FLTL
  | FLTL :/\ FLTL
  | Not FLTL
  | X FLTL
  | Xweak FLTL
  | F FLTL
  | G FLTL
  | U FLTL FLTL
  | R FLTL FLTL
  deriving (Eq, Ord)

instance Show FLTL where
  show TTrue = "true"
  show FFalse = "false"
  show (Prop x) = show x
  show (p :\/ q) = show p ++ " or " ++ show q
  show (p :/\ q) = show p ++ " and " ++ show q
  show (Not p) = "not " ++ show p
  show (X p) = "X " ++ show p
  show (Xweak p) = "Xweak " ++ show p
  show (G p) = "G " ++ show p
  show (F p) = "F " ++ show p
  show (U p q) = show p ++ " U " ++ show q
  show (R p q) = show p ++ " R " ++ show q

--  Negation Normal Form
nnf :: FLTL -> FLTL
nnf (Not (a :/\ b)) = Not (nnf a) :\/ Not (nnf b)
nnf (Not (a :\/ b)) = Not (nnf a) :/\ Not (nnf b)
nnf (Not (U a b)) = R (Not (nnf a)) (Not (nnf b))
nnf (Not (R a b)) = U (Not (nnf a)) (Not (nnf b))
nnf (Not (G a)) = F (Not (nnf a))
nnf (Not (F a)) = G (Not (nnf a))
nnf (Not (X a)) = Xweak (Not (nnf a))
nnf (Not (Xweak a)) = X (Not (nnf a))
nnf a = a

evlFLTL4 :: Char -> FLTL -> (Truth, FLTL)
evlFLTL4 a TTrue = (Top, TTrue)
evlFLTL4 a FFalse = (Bot, FFalse)
evlFLTL4 a (Prop p)
  | a == p = (Top, TTrue)
  | a /= p = (Bot, FFalse)
evlFLTL4 a (Not (Prop p))
  | a == p = (Bot, FFalse)
  | a /= p = (Top, TTrue)
evlFLTL4 a (l :\/ r) = (vl ⊔ vr, l' :\/ r')
  where
    (vl, l') = evlFLTL4 a l
    (vr, r') = evlFLTL4 a r
evlFLTL4 a (l :/\ r) = (vl ⊓ vr, l' :/\ r')
  where
    (vl, l') = evlFLTL4 a l
    (vr, r') = evlFLTL4 a r
evlFLTL4 a (X p) = (PBot, p)
evlFLTL4 a (Xweak p) = (PTop, p)
evlFLTL4 a (U p q) = (PTop, q :\/ (p :/\ X (U p q)))
evlFLTL4 a (R p q) = (PTop, q :/\ (p :\/ Xweak (R p q)))
evlFLTL4 a (F p) = evlFLTL4 a (p :\/ X (F p))
evlFLTL4 a (G p) = evlFLTL4 a (p :/\ Xweak (G p))

(-->) = Rule

data OperatorTerm
  = PropT Char
  | And
  | Or
  | Gop
  | Fop
  | Xop
  | Xweakop
  | Uop
  | Rop
  | Nop
  | TrueTerm
  | FalseTerm
  deriving (Eq, Show, Ord)

encode :: FLTL -> Term OperatorTerm Char
encode TTrue = truet
encode FFalse = falset
encode (φ1 :/\ φ2) = Fun And [encode φ1, encode φ2]
encode (φ1 :\/ φ2) = Fun Or [encode φ1, encode φ2]
encode (Prop x) = prop x
encode (Not (Prop x)) = Fun Nop [prop x]
encode (G φ) = Fun Gop [encode φ]
encode (F φ) = Fun Fop [encode φ]
encode (X φ) = Fun Xop [encode φ]
encode (Xweak φ) = Fun Xweakop [encode φ]
encode (φ1 `U` φ2) = Fun Uop [encode φ1, encode φ2]
encode (φ1 `R` φ2) = Fun Rop [encode φ1, encode φ2]

decode :: Term OperatorTerm Char -> FLTL
decode (Fun TrueTerm _) = TTrue
decode (Fun FalseTerm _) = FFalse
decode (Fun (PropT x) _) = Prop x
decode (Fun Nop (p : _)) = Not (decode p)
decode (Fun Gop (p : _)) = G (decode p)
decode (Fun Fop (p : _)) = F (decode p)
decode (Fun Xop (p : _)) = X (decode p)
decode (Fun Xweakop (p : _)) = Xweak (decode p)
decode (Fun Uop (φ1 : φ2 : _)) = decode φ1 `U` decode φ2
decode (Fun Rop (φ1 : φ2 : _)) = decode φ1 `R` decode φ2
decode (Fun And (φ1 : φ2 : _)) = decode φ1 :/\ decode φ2
decode (Fun Or (φ1 : φ2 : _)) = decode φ1 :\/ decode φ2

x = Var 'x'

y = Var 'y'

z = Var 'z'

prop :: Char -> Term OperatorTerm v
prop x = Fun (PropT x) []

ort :: [Term OperatorTerm Char] -> Term OperatorTerm Char
ort = Fun Or

andt :: [Term OperatorTerm Char] -> Term OperatorTerm Char
andt = Fun And

truet :: Term OperatorTerm Char
truet = Fun TrueTerm []

falset :: Term OperatorTerm Char
falset = Fun FalseTerm []

trs :: [Rule OperatorTerm Char]
trs =
  [ andt [truet, x] --> x,
    andt [x, truet] --> x,
    andt [falset, x] --> falset,
    andt [x, falset] --> falset,
    andt [x, x] --> x,
    ort [truet, x] --> truet,
    ort [x, truet] --> truet,
    ort [falset, x] --> x,
    ort [x, falset] --> x,
    ort [x, x] --> x,
    -- put in DNF
    andt [x, ort [y, z]] --> ort [andt [x, y], andt [x, z]],
    andt [ort [x, y], z] --> ort [andt [x, z], andt [y, z]]
  ]

nf trs trm = case Rules.fullRewrite trs trm of
  [] -> trm
  x : _ -> nf trs (result x)

simplfy :: FLTL -> FLTL
simplfy f = decode $ nf trs (encode f)

δ4 :: (FLTL, Char) -> (Truth, FLTL)
δ4 (TTrue, _) = (Top, TTrue)
δ4 (FFalse, _) = (Bot, FFalse)
δ4 (Prop p, a)
  | p == a = (Top, TTrue)
  | otherwise = (Bot, FFalse)
δ4 (Not (Prop p), a)
  | p /= a = (Top, TTrue)
  | otherwise = (Bot, FFalse)
δ4 (X φ, a) = (PBot, φ)
δ4 (Xweak φ, a) = (PTop, φ)
δ4 (φ1 :/\ φ2, a) = (vφ1 ⊓ vφ2, simplfy (φ1' :/\ φ2'))
  where
    (vφ1, φ1') = δ4 (φ1, a)
    (vφ2, φ2') = δ4 (φ2, a)
δ4 (φ1 :\/ φ2, a) = (vφ1 ⊔ vφ2, simplfy (φ1' :\/ φ2'))
  where
    (vφ1, φ1') = δ4 (φ1, a)
    (vφ2, φ2') = δ4 (φ2, a)
δ4 (f@(φ1 `U` φ2), a) = δ4 (φ2 :\/ (φ1 :/\ X f), a)
δ4 (f@(φ1 `R` φ2), a) = δ4 (φ2 :/\ (φ1 :\/ Xweak f), a)
δ4 (f@(F φ), a) = δ4 (φ :\/ X f, a)
δ4 (f@(G φ), a) = δ4 (φ :/\ Xweak f, a)

countingMealy = unfoldMealy (\i x -> ((i, x), i + 1)) 0

fltlMealy :: FLTL -> Mealy Char (Truth, FLTL)
fltlMealy = unfoldMealy (\f a -> let (t, g) = δ4 (f, a) in ((t, g), g))

mealy :: FLTL -> Map (FLTL, Char) (Truth, FLTL) -> [Char] -> Map (FLTL, Char) (Truth, FLTL)
mealy φ δ inputs =
  let newTransitions = fromList $ fmap (\i -> ((φ, i), δ4 (φ, i))) inputs
   in let newStates = fmap snd (elems newTransitions)
       in let visitedStates = fmap snd (elems δ)
           in let unexploredStates = newStates \\ visitedStates
               in let t = fmap (\s -> mealy s (δ `union` newTransitions) inputs) unexploredStates
                   in foldl union δ t

evlFLTL4Mealy :: FLTL -> Mealy Char ((Truth, FLTL), Char)
evlFLTL4Mealy = unfoldMealy (\s e -> let (emit, tgt) = evlFLTL4 e s in (((emit, s), e), simplfy tgt))

runMonitor :: (Foldable f) => f Char -> FLTL -> [(Truth, FLTL)]
runMonitor events φ = fst <$> run (auto (evlFLTL4Mealy φ) <~ source events)