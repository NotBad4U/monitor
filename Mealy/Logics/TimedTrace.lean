import Mathlib.Basic.NNReal.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Tactic.FinCases
import Init.Data.Vector.Basic

open NNReal
open ENNReal

variable (α : Type u) [DecidableEq α]

structure TimedTrace (n:Nat) where
  mk ::
  seq : Vector (α × ℝ≥0∞) n
  wff_seq : ∀ i j:Fin n, i < j -> (seq.get i).2 <= (seq.get j).2

-- Smart constructor

def TimedTrace.ofList (l : List (α × ℝ≥0∞))
    (h : l.Pairwise (fun x y => x.2 ≤ y.2)) : TimedTrace α l.length where
  seq := ⟨l.toArray, by simp⟩
  wff_seq := by
    intro i j hij
    have hij_all := List.pairwise_iff_getElem.mp h i j i.isLt j.isLt (Fin.lt_def.mp hij)
    simp [Vector.get]
    exact hij_all

def exemple : TimedTrace String 2 :=
  TimedTrace.ofList String [("a",1), ("a",2)] (by simp)

-- get_at

def get_at {n:Nat} (t:TimedTrace α n) (i:Fin n) : (α × ℝ≥0∞) :=
  t.seq.get i

-- last

def last {n:Nat} (t:TimedTrace α n) : Option (α × ℝ≥0∞) :=
  t.seq.back?

-- drop_off

def drop_off {n : Nat} (t : TimedTrace α n) (j : Fin n) : TimedTrace α (n - j.val) where
  seq := t.seq.drop j
  wff_seq := by
    intro a b hab
    simp [Vector.get]
    exact t.wff_seq ⟨j.val + a.val, by omega⟩ ⟨j.val + b.val, by omega⟩
      (by simp only [Fin.lt_def]; omega)

-- add

def add {n : Nat} (t : TimedTrace α n) (a : α × ℝ≥0∞) :  TimedTrace α (n + 1) := sorry
  sorry
