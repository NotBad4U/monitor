import Mathlib.Data.Finset.Lattice.Fold
import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4

import Mealy.Logics.TimedTrace
import Mealy.Logics.Range
import Mealy.Logics.MFLTL4.Syntax

open MFLTL4

namespace MFLTL4

universe u
variable {α : Type u} [DecidableEq α]
variable {τ : Type u} [Sub τ] [LinearOrder τ]

def lookup {n:ℕ} (w : TimedTrace α τ (n+1)) (i : ℕ) (x : α) : Bool :=
  match w.get_at? (i - 1) with
  | .some (x',_) => x' = x
  | .none => false

/--
  Notations and syntax extensions
-/
syntax:50 (name := memAt) term:51 " ∈ " ident "[" term "]" : term
macro_rules (kind := memAt)
  | `($x ∈ $w:ident[$i]) => `(lookup $w $i $x)

syntax:50 (name := notMemAt) term:51 " ∉ " ident "[" term "]" : term
macro_rules (kind := notMemAt)
  | `($x ∉ $w:ident[$i]) => `((lookup $w $i $x)ᶜ)

set_option hygiene false in
notation:200 "⟦ " w " , " i " ⊨ " p " ⟧₄" => sem w i p

set_option hygiene false in
notation:200 "⟦ " b " ⟧₂" => if b then .top else .bot

set_option hygiene false in
notation:200 i " ∈ᵢ " I => Range.contains I i

set_option hygiene false in
notation:200 i " ∉ᵢ " I => Range.contains I i = false

syntax:50 (name := supLt) " ⨆ " term:51 " ≤ " ident " ≤ " term:51 ", " term:51 : term
macro_rules (kind := supLt)
  | `(⨆ $i ≤ $j ≤ $k , $f) => `((Finset.Icc $i $k).sup fun $j => $f)

syntax:50 (name := infLt) " ⨅ " term:51 " ≤ " ident " ≤ " term:51 ", " term:51 : term
macro_rules (kind := infLt)
  | `(⨅ $i ≤ $j ≤ $k , $f) => `((Finset.Icc $i $k).inf fun $j => $f)

def foo {n:ℕ} (i  j: ℕ) (w : TimedTrace α τ (n+1)) (l: τ → τ → 𝔹₄) (r: 𝔹₄) : 𝔹₄ :=
  match w.get_at? i, w.get_at? j with
      | some (_, τi), some (_, τi1) => l τi τi1
      | _, _ => r

/--
  MFLTL₄ semantic
-/
def sem {n:ℕ} (w : TimedTrace α τ (n+1)) (i:ℕ): φ α τ → 𝔹₄
  | .true => ⊤
  | .false => ⊥
  | ⟨x⟩ => if x ∈ w[i] then ⊤ else ⊥
  | ~ ⟨x⟩ => if x ∉ w[i] then ⊤ else ⊥
  | ~ φ => (⟦ w , i  ⊨ φ ⟧₄)ᶜ
  | φ ⋀ ψ => ⟦ w , i  ⊨ φ ⟧₄ ⊓ ⟦ w , i ⊨ ψ ⟧₄
  | .next I φ =>
      foo i (i+1) w (fun τi τi1 => ⟦ (τi1 - τi) ∈ᵢ I ⟧₂ ⊓ ⟦ w , i + 1 ⊨ φ ⟧₄) ⊥ₚ
  | .weak_next I φ =>
      foo i (i+1) w (fun τi τi1 => ⟦ (τi1 - τi) ∈ᵢ I ⟧₂ ⊓ ⟦ w , i + 1 ⊨ φ ⟧₄) ⊤ₚ
  | .until I φ ψ => sorry
  --         (⨆ i ≤ j ≤ |w|, (⟦ ((I.get_at j) - (I.get_at i)) ∈ᵢ I ⟧₂ ⊓ ⟦ w , j ⊨ ψ ⟧₄ ⊓ (⨅ i ≤ k ≤ j, ⟦ w , k ⊨ φ ⟧₄)))
  --       ⊔ (⊥ₚ ⊓ ⟦ I.last ≤ τi + I.max ⟧₂ ⊓ (⨅ i ≤ k ≤ |w|, ⟦ w , k ⊨ φ ⟧₄))
  | .release I φ ψ => sorry
  --           (⨅ i ≤ j ≤ |w|, ⟦ (τj - τi) ∉ᵢ I ⟧₂ ⊔ ⟦ w , j ⊨ ψ ⟧₄ ⊔ (⨆ i ≤ k ≤ j, ⟦ w , k ⊨ φ ⟧₄))
  --           ⊓ (⊤ₚ ⊔ ⟦ I.last > τi + I.max ⟧₂ ⊔ (⨆ i ≤ k ≤ |w|, ⟦ w , k ⊨ φ ⟧₄))
