import Mathlib.Basic.NNReal.Basic
import Mathlib.Basic.ENNReal.Basic
import Init.Data.Vector.Basic

open NNReal
open ENNReal

variable (α : Type u) [DecidableEq α]

structure TimedTrace {n:Nat} where
  mk ::
  seq : Vector (α × ℝ≥0∞) n
  wff_seq : ∀ i:Fin n, ∀ j:Fin n, i < j -> j <= n -> (seq.get i).2 <= (seq.get j).2

-- add

-- drop_off

-- get_at

-- member

-- last
