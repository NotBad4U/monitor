import Mathlib.Data.PFunctor.Univariate.Basic
import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4
import Mealy.Logic.Syntax

variable (α : Type u) [DecidableEq α]

def run : α → φ α → 𝔹₄ × φ α
  | _, .true  => (.top, .true)
  | _, .false => (.bot, .false)
  | a, .ap p  => if a = p then (.top, .true) else (.bot, .false)
  | a, .not (.ap p) => if a = p then (.bot, .false) else (.top, .true)
  | a, .not f =>
    let (v, f') := run a f
    (vᶜ, .not f')
  | a, .or f g =>
    let (vf, f') := run a f
    let (vg, g') := run a g
    (max vf vg, .or f' g')
  | a, .and f g =>
    let (vf, f') := run a f
    let (vg, g') := run a g
    (min vf vg, .and f' g')
  | _, .next f      => (.botₚ, f)
  | _, .weak_next f => (.topₚ, f)
  -- f U g  ≡  g ∨ (f ∧ X (f U g))
  | a, .until f g =>
    let (vf, f') := run a f
    let (vg, g') := run a g
    (max vg (min vf .botₚ),
     .or g' (.and f' (.next (.until f g))))
  -- f R g  ≡  g ∧ (f ∨ X̅ (f R g))
  | a, .release f g =>
    let (vf, f') := run a f
    let (vg, g') := run a g
    (min vg (max vf .topₚ),
     .and g' (.or f' (.weak_next (.release f g))))
  -- F f  ≡  f ∨ X F f
  | a, .finally f =>
    let (vf, f') := run a f
    (max vf .botₚ, .or f' (.next (.finally f)))
  -- G f  ≡  f ∧ X̅ G f
  | a, .globally f =>
    let (vf, f') := run a f
    (min vf .topₚ, .and f' (.weak_next (.globally f)))
