import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice

-- This is already defined in Mathlib.Order.BooleanAlgebra
class BooleanLattice (A : Type) extends Lattice A, BoundedOrder A, Compl A

/-
  Notations are introduced in the Lattice class as follow:
  - a ⊔ b: the supremum or join of a and b
  - a ⊓ b: the infimum or meet of a and b
-/

class BooleanLatticeProperties (A : Type) extends BooleanLattice A where
  commut_cap : ∀ a b : A, a ⊓ b = b ⊓ a
  commut_cup : ∀ a b: A, a ⊔ b = b ⊔ a
  assoc_cap : ∀ a b c : A, a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c
  assoc_cup : ∀ a b c : A, a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c
  distr_cap : ∀ a b c : A, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
  distr_cup : ∀ a b c : A, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)

class BooleanNegationProperties (A : Type) extends BooleanLattice A where
  not_not : ∀ a : A, a ᶜ ᶜ = a
