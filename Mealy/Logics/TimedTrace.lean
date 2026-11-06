import Mathlib.Tactic.FinCases
import Init.Data.Vector.Basic

universe u v in
variable (α : Type u) [DecidableEq α] in
variable (τ : Type v) [LE τ] in
structure TimedTrace (n:Nat) where
  mk ::
  seq : Vector (α × τ) n
  -- Explore why `_[_]` is more adapted for proof than `_.get _`.
  wff_seq : ∀ i j:Fin n, i < j -> seq[i].2 ≤ seq[j].2

-- Smart constructor

def TimedTrace.ofList {α} {τ} [LE τ] (l : List (α × τ))
    (h : l.Pairwise (fun x y => x.2 ≤ y.2)) : TimedTrace α τ l.length where
  seq := ⟨l.toArray, by simp⟩
  wff_seq := by
    intro i j hij
    exact List.pairwise_iff_getElem.mp h i j i.isLt j.isLt (Fin.lt_def.mp hij)

-- last

def TimedTrace.last {α} {τ} [LE τ] {n:Nat} (t:TimedTrace α τ (n + 1)) : (α × τ) :=
  t.seq.back

def TimedTrace.last? {α} {τ} [LE τ] {n:Nat} (t:TimedTrace α τ n) : Option (α × τ) :=
  t.seq.back?

-- add

def TimedTrace.add {α} {τ} [LE τ] [DecidableEq α] {n : Nat} (t : TimedTrace α τ n) (a : α × τ)
    (h : ∀ b: Fin n, t.seq[b].2 ≤ a.2) : TimedTrace α τ (n + 1) where
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

def TimedTrace.get_at {α} {τ} [LE τ] {n:Nat} (t:TimedTrace α τ n) (i:Fin n) : (α × τ) :=
  t.seq.get i

-- drop_off

def TimedTrace.drop_off {α} {τ} [LE τ] {n : Nat} (t : TimedTrace α τ n) (j : Fin n) : TimedTrace α τ (n - j.val) where
  seq := t.seq.drop j
  wff_seq := by
    intro a b hab
    simp [Vector.drop]
    exact t.wff_seq ⟨j.val + a.val, by omega⟩ ⟨j.val + b.val, by omega⟩ (by simp only [Fin.lt_def]; omega)

-- Examples

namespace Examples

def ex1 : TimedTrace String Nat 2 :=
  TimedTrace.ofList [("a",1), ("a",2)] (by simp)

def ex2 : TimedTrace String Nat 3 :=
  ex1.add ("a",2) (by simp [ex1, TimedTrace.ofList])

end Examples

-- Properties

theorem add_last {α} [DecidableEq α] {τ} [LE τ] {n : Nat} :
  ∀ t : TimedTrace α τ n, ∀ a : (α × τ), (h : ∀ b: Fin n, t.seq[b].2 ≤ a.2) →
  (t.add a (by exact h)).last = a := by
  intro t x
  simp [TimedTrace.add, TimedTrace.last, Vector.push, Array.push]
