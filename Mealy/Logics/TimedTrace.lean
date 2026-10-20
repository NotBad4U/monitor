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
  -- Explore why `_[_]` is more adapted for proof than `_.get _`.
  wff_seq : ∀ i j:Fin n, i < j -> seq[i].2 <= seq[j].2

-- Smart constructor

def TimedTrace.ofList (l : List (α × ℝ≥0∞))
    (h : l.Pairwise (fun x y => x.2 ≤ y.2)) : TimedTrace α l.length where
  seq := ⟨l.toArray, by simp⟩
  wff_seq := by
    intro i j hij
    exact List.pairwise_iff_getElem.mp h i j i.isLt j.isLt (Fin.lt_def.mp hij)

-- last

def TimedTrace.last? {n:Nat} (t:TimedTrace α n) : Option (α × ℝ≥0∞) :=
  t.seq.back?

-- add

def TimedTrace.add {n : Nat} (t : TimedTrace α n) (a : α × ℝ≥0∞)
    (h : ∀ b: Fin n, t.seq[b].2 ≤ a.2) : TimedTrace α (n + 1) where
  seq := t.seq.push a
  wff_seq := by
    intro i j hij
    have hi : i.val < n := by have := Fin.lt_def.mp hij; omega
    by_cases hj : j.val < n
    · simp [hi, hj]
      exact t.wff_seq ⟨i.val, hi⟩ ⟨j.val, hj⟩ (by simp only [Fin.lt_def]; omega)
    · simp [Vector.getElem_push, hi, hj]
      exact h ⟨i.val, hi⟩

-- get_at

def TimedTrace.get_at {n:Nat} (t:TimedTrace α n) (i:Fin n) : (α × ℝ≥0∞) :=
  t.seq.get i

-- drop_off

def TimedTrace.drop_off {n : Nat} (t : TimedTrace α n) (j : Fin n) : TimedTrace α (n - j.val) where
  seq := t.seq.drop j
  wff_seq := by
    intro a b hab
    simp [Vector.drop]
    exact t.wff_seq ⟨j.val + a.val, by omega⟩ ⟨j.val + b.val, by omega⟩ (by simp only [Fin.lt_def]; omega)

-- Examples

def ex1 : TimedTrace String 2 :=
  TimedTrace.ofList String [("a",1), ("a",2)] (by simp)

def ex2 : TimedTrace String 3 :=
  ex1.add String ("a",2) (by simp [ex1, TimedTrace.ofList])
