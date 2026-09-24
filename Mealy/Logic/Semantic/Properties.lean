import Mathlib.Data.Finset.Lattice.Fold

import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4

import Mealy.Logic.Syntax
import Mealy.Logic.Semantic.Denotation

variable {α} [DecidableEq α]

/--
  Put a formula φ into a Negation Normal Form i.e negation on the leaves
-/
def nnf : φ α → φ α
  | ~ .true => .false
  | ~ .false => .true
  | ~ ⟨x⟩ => ~ ⟨x⟩
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
  | ⟨x⟩ => ⟨x⟩

-- Decidable predicate to check if a formula φ is in Negation Normal Form
def is_nnf : φ α → Bool
  | ~ .true => false
  | ~ .false => false
  | ~ ⟨_⟩ => true
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
  | ⟨_⟩ => true

omit [DecidableEq α] in
theorem nnf_is_nnf (f : φ α) : is_nnf (nnf f) = true := by
  induction f using nnf.induct <;> simp_all [is_nnf, nnf]

omit [DecidableEq α] in
theorem nnf_impl (a b : φ α) : nnf (a ⟶ b) = nnf (~ a) ⋁ nnf b := by simp [nnf]

@[simp]
lemma inf_top_eq_top (i : ℕ) : (⨅ _j < i, 𝔹₄.top) = 𝔹₄.top := by apply Finset.inf_top _

@[simp]
lemma sup_top_eq_top (i : ℕ) (hi : 0 < i) : (⨆ _j < i, 𝔹₄.top) = 𝔹₄.top := by
  apply Finset.sup_const
  exact ⟨0, Finset.mem_range.mpr hi⟩

@[simp]
lemma sup_bot_eq_bot (i : ℕ) : (⨆ _j < i, 𝔹₄.bot) = 𝔹₄.bot := by apply Finset.sup_bot _

@[simp]
lemma inf_bot_eq_bot (i : ℕ) (hi : 0 < i) : (⨅ _j < i, 𝔹₄.bot) = 𝔹₄.bot := by
  apply Finset.inf_const
  exact ⟨0, Finset.mem_range.mpr hi⟩

@[simp]
lemma compl_range_sup (n : ℕ) (f : ℕ → 𝔹₄) : (⨆ i ∈ n, f i)ᶜ = (⨅ i ∈ n, (f i)ᶜ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finset.range_add_one, ih]

@[simp]
lemma compl_range_inf (n : ℕ) (f : ℕ → 𝔹₄) : (⨅ i ∈ n, f i)ᶜ = (⨆ i ∈ n, (f i)ᶜ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finset.range_add_one, ih]

-- Semantic equivalence between 𝑮𝜑 and ¬𝑭¬𝜑
lemma equiv_G (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ = ⟦ w ⊨ ~ 𝑭 (~ f) ⟧ := by
  simp only [sem]
  simp only [sem_not_eq_compl_sem]
  simp [compl_range_sup]

-- Semantic equivalence between 𝑭𝜑 and ¬𝑮¬𝜑
lemma equiv_F (w : List α) (f : φ α) : ⟦ w ⊨ 𝑭 f ⟧ = ⟦ w ⊨ ~ 𝑮 (~ f) ⟧ := by
  simp only [sem]
  simp only [sem_not_eq_compl_sem]
  simp [compl_range_inf]

@[simp]
lemma compl_ite₄ (c : Prop) [Decidable c] (a b : 𝔹₄) :
    (if c then a else b)ᶜ = if c then aᶜ else bᶜ := by split <;> rfl

theorem sem_nnf_equiv (w : List α) (f : φ α) : ⟦ w ⊨ nnf f ⟧ = ⟦ w ⊨ f ⟧ := by
  induction f using nnf.induct generalizing w <;> simp_all [nnf, sem, nlookup]

lemma sem_impl (w : List α) (a b : φ α) : ⟦ w ⊨ a ⟶ b ⟧ = (⟦ w ⊨ a ⟧ ⇒ ⟦ w ⊨ b ⟧) := by
  simp [sem, impl_def₄]

-- https://en.wikipedia.org/wiki/Modal_logic

lemma join_inf_le_inf_join [Lattice A] [OrderTop A] (n : ℕ) (f g : ℕ → A) :
    (⨅ i < n, f i) ⊔ (⨅ i < n, g i) ≤ ⨅ i < n, (f i ⊔ g i) :=
  Finset.le_inf fun _i hi => sup_le_sup (Finset.inf_le hi) (Finset.inf_le hi)

-- ⨆ i < n, (f i ⊓ g i) ≤ (⨆ i < n, f i) ⊓ (⨆ i < n, g i)
lemma meet_inf_le_inf_meet [Lattice A] [OrderBot A] (n : ℕ) (f g : ℕ → A) :
    (⨆ i < n, (f i ⊓ g i)) ≤ (⨆ i < n, f i) ⊓ (⨆ i < n, g i) :=
  Finset.sup_le fun _i hi => inf_le_inf (Finset.le_sup hi) (Finset.le_sup hi)

lemma inf_join_le_join_sup_inf [DistribLattice A] [BoundedOrder A] (n : ℕ) (f g : ℕ → A) :
    (⨅ i < n, (f i ⊔ g i)) ≤ (⨆ i < n, f i) ⊔ (⨅ i < n, g i) := by
  rw [Finset.inf_sup_distrib_left]
  exact Finset.inf_mono_fun (fun _i hi => sup_le_sup_right (Finset.le_sup (f := f) hi) _)

-- K i.e. arbitrary Kripke frame : □ (a → b) ⊢ □ a → □ b
theorem sem_frame (w : List α) (a b : φ α) : ⟦ w ⊨ 𝑮 (a ⟶ b) ⟧ ≤ ⟦ w ⊨ (𝑮 a) ⟶ (𝑮 b) ⟧ := by
  simp only [sem, sem_not_eq_compl_sem]
  set n := |w|
  set A := fun i => ⟦ w^i ⊨ a ⟧ with hA
  set B := fun i => ⟦ w^i ⊨ b ⟧ with hB
  show ⊤ₚ ⊓ (⨅ i < n, ((A i)ᶜ ⊔ B i)) ≤ (⊤ₚ ⊓ (⨅ i < n, A i))ᶜ ⊔ (⊤ₚ ⊓ (⨅ i < n, B i))
  simp_rw [BooleanLatticeProperties_𝔹₄.distr_cup]
  simp
  simp_rw [← BooleanLatticeProperties_𝔹₄.assoc_cup, ← compl_range_inf]
  calc
    ⊤ₚ ⊓ (⨅ i < n, ((A i)ᶜ ⊔ B i)) ≤ ⨅ i < n, ((A i)ᶜ ⊔ B i) := inf_le_right
    _ ≤ (⨆ i < n, (A i)ᶜ) ⊔ (⨅ i < n, B i) := inf_join_le_join_sup_inf n (fun i => (A i)ᶜ) B
    _ = (⨅< n, A)ᶜ ⊔ (⨅ i < n, B i) := by rw [compl_range_inf]
    _ ≤ ⊥ₚ ⊔ ((⨅< n, A)ᶜ ⊔ (⨅ i < n, B i)) := le_sup_right

lemma split_const_left_inf (m : ℕ) (g : ℕ → 𝔹₄) (c : 𝔹₄) :
    (⨅ i < m, (c ⊓ g i)) = (⨅ _i < m, c) ⊓ (⨅ i < m, g i) := by
  rw [← Finset.inf_inf]
  rfl

lemma split_const_sup_right_left (m : ℕ) (g : ℕ → 𝔹₄) (c : 𝔹₄) :
    (⨆ i < m, (c ⊔ g i)) = (⨆ _i < m, c) ⊔ (⨆ i < m, g i) := by
  rw [← Finset.sup_sup]
  rfl

-- 4 i.e transitivity : □p ⊢ □□p
theorem sem_transitivity_G (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑮 f ⟧ := by
  simp only [sem]
  set n := |w|
  rw [split_const_left_inf]
  refine le_inf inf_le_left (le_inf (le_trans inf_le_left Finset.le_inf_const) ?_)
  refine Finset.le_inf fun i hi => Finset.le_inf fun j hj => ?_
  rw [List.drop_drop]
  refine le_trans inf_le_right (Finset.inf_le ?_)
  simp only [Finset.mem_range, List.length_drop] at *
  lia

-- T i.e. reflexivity □p ⊢ p
theorem sem_reflexivity_G (w : List α) (hw : 0 < |w|) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ f ⟧ := by
  simp only [sem]
  calc
    ⊤ₚ ⊓ (⨅ i < |w|, ⟦ w^i ⊨ f ⟧) ≤ ⨅ i < |w|, ⟦ w^i ⊨ f ⟧ := inf_le_right
    _ ≤ ⟦ w^0 ⊨ f ⟧ := Finset.inf_le (Finset.mem_range.mpr hw)
    _ = ⟦ w ⊨ f ⟧ := by rw [List.drop_zero]

-- 𝑮 p will never be greather than ⊤ by design of sem
lemma sem_G_le_topₚ (w : List α) (g : φ α) : ⟦ w ⊨ 𝑮 g ⟧ ≤ ⊤ₚ :=
  inf_le_left

-- 𝑭 p will always be greather than ⊥ₚ by design of sem
lemma sem_F_le_botₚ (w : List α) (g : φ α) : ⊥ₚ ≤ ⟦ w ⊨ 𝑭 g ⟧ :=
  le_sup_left

-- 𝑮 p will never be ⊤ by design of sem
lemma sem_G_neq_top (w : List α) (g : φ α) : ⟦ w ⊨ 𝑮 g ⟧ ≠ 𝔹₄.top := by
  simp only [sem]
  intro h
  rw [top_eq₄, inf_eq_top_iff] at h
  exact 𝔹₄.noConfusion h.1

-- 𝑭 p will never be ⊥ by design of sem
lemma sem_F_neq_bot (w : List α) (g : φ α) : ⊥ₚ ≤ ⟦ w ⊨ 𝑭 g ⟧ :=
  le_sup_left

-- 𝑮 is monotone along suffixes i.e. 𝑮 truth value can only get better
lemma sem_G_le_G_drop (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w^1 ⊨ 𝑮 f ⟧ := by
  simp only [sem]
  refine le_inf inf_le_left (le_trans inf_le_right (Finset.le_inf fun i hi => ?_))
  rw [List.drop_drop]
  refine Finset.inf_le ?_
  simp only [Finset.mem_range, List.length_drop] at *
  lia

--  𝑭 is antitone along suffixes i.e. 𝑭 truth value can only get worse as time passes;
lemma sem_F_drop_le_F (w : List α) (f : φ α) : ⟦ w^1 ⊨ 𝑭 f ⟧ ≤ ⟦ w ⊨ 𝑭 f ⟧ := by
  simp only [sem]
  refine sup_le_sup_left (Finset.sup_le fun i hi => ?_) _
  rw [List.drop_drop]
  refine Finset.le_sup (f := fun j => ⟦ w^j ⊨ f ⟧) ?_
  simp only [Finset.mem_range, List.length_drop] at *
  lia

-- B i.e. symmetry p ⊢ □♢p : does NOT hold
-- Witness: w = [0, 1] and f = ⟨0⟩, where ⟦ w ⊨ f ⟧ = ⊤ but ⟦ w ⊨ 𝑮 𝑭 f ⟧ = ⊥ₚ.
theorem not_sem_symmetry : ¬∀ (w : List ℕ) (f : φ ℕ), ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ := fun h =>
  h [0, 1] ⟨0⟩

-- T dual i.e. reflexivity p ⊢ ◊p
-- NOTE: the proof can be also done with using equiv_F
lemma sem_reflexivity_F (w : List α) (hw : 0 < |w|) (f : φ α) : ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑭 f ⟧ := by
  simp only [sem]
  refine le_sup_of_le_right ?_
  have hz : ⟦ w ⊨ f ⟧ = ⟦ w^0 ⊨ f ⟧ := by rw [List.drop_zero]
  rw [hz]
  have w_nonempty : 0 ∈ (Finset.range w.length) := Iff.mpr Finset.mem_range hw
  exact Finset.le_sup (f := fun j => ⟦ w^j ⊨ f ⟧) w_nonempty

-- The T property (□p ⊢ p) and its dual (p ⊢ ♢p) principle can be proven from equiv_F and equiv_G
example (w : List α) (hw : 0 < |w|) (f : φ α) : ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑭 f ⟧ := by
  have h := sem_reflexivity_G w hw (~ f)
  rw [sem_not_eq_compl_sem] at h
  have h2 := compl_le_compl₄ h
  rw [compl_compl₄] at h2
  rw [equiv_F, sem_not_eq_compl_sem]
  exact h2

example (w : List α) (hw : 0 < |w|) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ f ⟧ := by
  have h := sem_reflexivity_F w hw (~ f)
  rw [sem_not_eq_compl_sem] at h
  have h2 := compl_le_compl₄ h
  rw [compl_compl₄] at h2
  rw [equiv_G, sem_not_eq_compl_sem]
  exact h2

-- D i.e. seriality ◻p ⊢ ◊p : holds exactly on nonempty words.
-- On `[]` it fails, since ⟦ [] ⊨ 𝑮 f ⟧ = ⊤ₚ while ⟦ [] ⊨ 𝑭 f ⟧ = ⊥ₚ.
theorem sem_serial (w : List α) (hw : 0 < |w|) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ 𝑭 f ⟧ := by
  refine le_trans (sem_reflexivity_G w hw f) ?_
  simp only [sem]
  exact sem_reflexivity_F w hw f

-- 5 i.e euclideanity ♢p ⊢ ◻◊p : does NOT hold
-- Witness: w = ["a"] and f = ⟨"a"⟩, where ⟦ w ⊨ 𝑭 f ⟧ = ⊤ but ⟦ w ⊨ 𝑮 𝑭 f ⟧ = ⊤ₚ.
lemma not_sem_euclideanity : ¬∀ (w : List String) (f : φ String), ⟦ w ⊨ 𝑭 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ :=
  fun h => h ["a"] ⟨"a"⟩

-- Corrolary from Modal properties

-- 𝑮 is monotone in its argument, position by position
lemma sem_G_mono (w : List α) (a b : φ α) (h : ∀ i, i < |w| → ⟦ w^i ⊨ a ⟧ ≤ ⟦ w^i ⊨ b ⟧) :
    ⟦ w ⊨ 𝑮 a ⟧ ≤ ⟦ w ⊨ 𝑮 b ⟧ := by
  simp only [sem]
  exact inf_le_inf_left ⊤ₚ (Finset.inf_mono_fun fun i hi => h i (Finset.mem_range.mp hi))

-- □p ⊢ □□p ⊢ □♢p holds because
lemma sem_G_le_G_F (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ :=
  le_trans (sem_transitivity_G w f) -- □p ⊢ □□p
    (sem_G_mono w (𝑮 f) (𝑭 f) fun i hi => -- □p ⊢ □q if p < q
      sem_serial (w^i)
        (by
          simp only [List.length_drop]; lia)
        f) -- □□p ⊢ □♢p

-- N i.e. Necessitation Rule p ⊢ □p
theorem sem_symmetry_of_le_G (w : List α) (f : φ α) (h : ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 f ⟧) :
    ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ :=
  le_trans h (sem_G_le_G_F w f)
