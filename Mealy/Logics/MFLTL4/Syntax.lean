import Mathlib.Basic.ENNReal.Basic

import Mealy.Logics.Range

namespace MFLTL4

-- uncomment for dev mode only
universe u
variable (α : Type u) [DecidableEq α]
variable (τ : Type u) [LinearOrder τ]

/--
  MFLTL algebraic data type
-/
inductive φ : Type u where
  | true : φ
  | false : φ
  | ap : α → φ
  | not : φ → φ
  | and : φ → φ → φ
  | next : 𝑰 τ → φ → φ
  | weak_next : 𝑰 τ → φ → φ
  | until : 𝑰 τ → φ → φ → φ
  | release : 𝑰 τ → φ → φ → φ
  deriving DecidableEq, Repr

variable {α}
variable {τ}

/--
  Syntax annotations
-/
prefix:60 "~ " => φ.not

infixr:130 " ⋀ " => φ.and

infixr:130 " ⋁ " => φ.or

prefix:75 "𝑿 " => φ.next

prefix:75 "X̅ " => φ.weak_next

notation l " 𝑼 " i r  => φ.until i l r

notation l " 𝑹" i r => φ.release i l r

notation "⟨ " e " ⟩" => φ.ap e

notation:130 (name := φ.impl) a " ⟶ " b => (~ a) ⋁ b

-- Normalisation

def MFLTL4.nrm : φ α τ → φ α τ
  | .true => .true
  | .false => .false
  | .ap a => .ap a
  | .not f =>
      match nrm f with
      | .true => .false
      | .false => .true
      | f => .not f
  | .and l r =>
      match nrm l, nrm r with
      | .true, r => r
      | .false, _ => .false
      | l, .true => l
      | _, .false => .false
      -- Consider range where interection is not empty
      | .next ρ e, .next ρ' e' =>
        if ρ.intersect ρ' && e = e'
        then .next (ρ ⊕ ρ') e
        else .and l r
      | .weak_next ρ e, .weak_next ρ' e' =>
        if ρ.intersect ρ' && e = e'
        then .weak_next (ρ ⊕ ρ') e
        else .and l r
      | .until ρ e f, .until ρ' e' f' =>
        if ρ.intersect ρ' && e = e' && f == f'
        then .until (ρ ⊕ ρ') e f
        else .and l r
      | .release ρ e f, .release ρ' e' f' =>
        if ρ.intersect ρ' && e = e' && f == f'
        then .release (ρ ⊕ ρ') e f
        else .and l r
      -- Final case
      | l, r => if l = r then l else .and l r
  | .next ρ e => .next ρ (nrm e)
  | .weak_next ρ e => .weak_next ρ (nrm e)
  | .until ρ l r => .until ρ (nrm l) (nrm r)
  | .release ρ l r => .release ρ (nrm l) (nrm r)

theorem MFLTL4.nrm_nrm_eq_nrm : ∀ e: φ α τ, nrm (nrm e) = nrm e := by
  intro e; induction e <;> grind [MFLTL4.nrm]
