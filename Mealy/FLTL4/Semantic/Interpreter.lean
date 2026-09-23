import Mathlib.Data.Finset.Lattice.Fold

import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4

import Mealy.FLTL4.Definition
import Mealy.FLTL4.NNF
import Mealy.FLTL4.Semantic.Notations

-- uncomment for dev mode only
set_option pp.parens true

variable {α} [DecidableEq α]

def sem (w : List α) : φ α → 𝔹₄
  | .true => ⊤
  | .false => ⊥
  | ~ ⟨ x ⟩ => x ∉ w[0]
  | ⟨ x ⟩ => x ∈ w[0]
  | ~ φ => (sem w φ)ᶜ
  | φ ⋁ ψ => sem w φ ⊔ sem w ψ
  | φ ⋀ ψ => sem w φ ⊓ sem w ψ
  | 𝑿 φ => if | w | > 0 then ⟦ w ^ 1 ⊨ φ ⟧ else ⊥ₚ
  | X̅ φ => if | w | > 0 then ⟦ w ^ 1 ⊨ φ ⟧ else ⊤ₚ
  | 𝑮 φ => ⊤ₚ ⊓ (⨅ i ∈ | w | , ⟦ w ^ i ⊨ φ ⟧)
  | 𝑭 φ => ⊥ₚ ⊔ (⨆ i ∈ | w | , ⟦ w ^ i ⊨ φ ⟧)
  | φ 𝑼 ψ =>
    (⨆ i ∈ | w | , (⟦ w ^ i ⊨ ψ ⟧ ⊓ (⨅ j ∈ i, ⟦ w ^ j ⊨ φ ⟧))) ⊔
      (⊥ₚ ⊓ (⨅ i ∈ | w | , ⟦ w ^ i ⊨ φ ⟧))
  | φ 𝑹 ψ =>
    (⨅ i ∈ | w | , (⟦ w ^ i ⊨ ψ ⟧ ⊔ (⨆ j ∈ i, ⟦ w ^ j ⊨ φ ⟧))) ⊓
      (⊤ₚ ⊔ (⨆ i ∈ | w | , ⟦ w ^ i ⊨ φ ⟧))

/--
  Semantic negation is the complement of the semantic
-/

@[simp]
lemma sem_not_eq_compl_sem (w : List α) (f : φ α) : ⟦ w ⊨ ~ f ⟧ = (⟦ w ⊨ f ⟧)ᶜ := by
  cases f with
  | ap x => simp [sem, nlookup]
  | _ => simp [sem]

/--
  Or, And commutativity
-/

@[simp]
lemma or_commutative :
    ∀ (w : List α), ∀ (a b : φ α), ⟦ w ⊨ a ⋁ b ⟧ = ⟦ w ⊨ b ⋁ a ⟧ := by
  intro w a b
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.commut_cup ..

@[simp]
lemma and_commutativity :
    ∀ (w : List α), ∀ (a b : φ α), ⟦ w ⊨ a ⋀ b ⟧ = ⟦ w ⊨ b ⋀ a ⟧ := by
  intro w a b
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.commut_cap ..

/--
  Or, And associativity
-/

@[simp]
lemma or_associativity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋁ (b ⋁ c) ⟧ = ⟦ w ⊨ (a ⋁ b) ⋁ c ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.assoc_cup ..

@[simp]
lemma and_associativity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋀ (b ⋀ c) ⟧ = ⟦ w ⊨ (a ⋀ b) ⋀ c ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.assoc_cap ..

/--
  Or/And, And/Or distributivity
-/

@[simp]
lemma or_and_distributivity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋁ (b ⋀ c) ⟧ = ⟦ w ⊨ (a ⋁ b) ⋀ (a ⋁ c) ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.distr_cup ..

@[simp]
lemma and_or_distributivity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋀ (b ⋁ c) ⟧ = ⟦ w ⊨ (a ⋀ b) ⋁ (a ⋀ c) ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.distr_cap ..

/--
  Semantic equivalences for constructions 𝑭 and 𝑮
-/

lemma eq_sem_F_with_U (w: List α ) (f: φ α) : ⟦ w ⊨ 𝑭 f ⟧ = ⟦ w ⊨ .true 𝑼 f ⟧ := by
   simp only [sem]
   simp [sup_comm]

lemma eq_sem_G_with_R (w: List α ) (f: φ α) : ⟦ w ⊨ 𝑮 f ⟧ = ⟦ w ⊨ .false 𝑹 f ⟧ := by
  simp only [sem]
  simp [inf_comm]
