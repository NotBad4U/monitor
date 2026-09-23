import Mealy.FLTL4.Definition

variable { α } [DecidableEq α]

-- uncomment for dev mode only
set_option pp.parens true

/--
  Put a formula φ into a Negation Normal Form i.e negation on the leaves
-/
def nnf : φ α → φ α
  | ~ .true => .false
  | ~ .false => .true
  | ~ ⟨ x ⟩ => ~ ⟨ x ⟩
  | ~ ~ φ => nnf φ
  | ~ (φ ⋁ ψ) => (nnf (~ φ)) ⋀ (nnf (~ ψ))
  | ~ (φ ⋀ ψ) => (nnf (~ φ)) ⋁ (nnf (~ ψ))
  | ~ 𝑿 φ => X̅ (nnf (~ φ))
  | ~ X̅ φ => 𝑿 (nnf (~ φ))
  | ~ 𝑮 φ => 𝑭 (nnf (~ φ))
  | ~ 𝑭 φ => 𝑮 (nnf (~ φ))
  | ~ (φ 𝑼 ψ) => (nnf (~ φ)) 𝑹 (nnf (~ ψ))
  | ~ (φ 𝑹 ψ) => (nnf (~ φ)) 𝑼 (nnf (~ ψ))
  | φ ⋀ ψ => (nnf φ) ⋀ (nnf ψ)
  | φ ⋁ ψ => (nnf φ) ⋁ (nnf ψ)
  | 𝑿 φ => 𝑿 (nnf φ)
  | X̅ φ => X̅ (nnf φ)
  | 𝑮 φ => 𝑮 (nnf φ)
  | 𝑭 φ => 𝑭 (nnf φ)
  | φ 𝑼 ψ => (nnf φ) 𝑼 (nnf ψ)
  | φ 𝑹 ψ => (nnf φ) 𝑹 (nnf ψ)
  | .true => .true
  | .false => .false
  | ⟨ x ⟩ => ⟨ x ⟩

-- Decidable predicate to check if a formula φ is in Negation Normal Form
def is_nnf : φ α → Bool
  | ~ .true => false
  | ~ .false => false
  | ~ ⟨ _ ⟩ => true
  | ~ ~ _ => false
  | ~ (_ ⋁ _) => false
  | ~ (_ ⋀ _) => false
  | ~ 𝑿 _ => false
  | ~ X̅ _ => false
  | ~ 𝑮 _ => false
  | ~ 𝑭 _ => false
  | ~ (_ 𝑼 _) => false
  | ~ (_ 𝑹 _) => false
  | φ ⋀ ψ => (is_nnf φ) && (is_nnf ψ)
  | φ ⋁ ψ => (is_nnf φ) && (is_nnf ψ)
  | 𝑿 φ => (is_nnf φ)
  | X̅ φ => (is_nnf φ)
  | 𝑮 φ => (is_nnf φ)
  | 𝑭 φ => (is_nnf φ)
  | φ 𝑼 ψ => (is_nnf φ) && (is_nnf ψ)
  | φ 𝑹 ψ => (is_nnf φ) && (is_nnf ψ)
  | .true => true
  | .false => true
  | ⟨ _ ⟩ => true

omit [DecidableEq α] in
theorem nnf_is_nnf (f : φ α) : is_nnf (nnf f) = true := by
  induction f using nnf.induct <;> simp_all [is_nnf, nnf]

omit [DecidableEq α] in
theorem nnf_impl (a b : φ α) : nnf (a ⟶ b) = nnf (~ a) ⋁ nnf b := by
  simp [nnf]
