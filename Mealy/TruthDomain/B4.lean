import Mealy.TruthDomain.Core

-- ====================================================================================
-- 𝔹₄
-- ====================================================================================

inductive 𝔹₄ where
  | bot
  | botₚ
  | topₚ
  | top

deriving instance BEq, Hashable for 𝔹₄

-- Notation for the two "presumably" values
notation "⊥ₚ" => 𝔹₄.botₚ

notation "⊤ₚ" => 𝔹₄.topₚ

-- Lets `#eval` print truth values as `⊥ / ⊥ₚ / ⊤ₚ / ⊤` instead of full constructor names
instance : Repr 𝔹₄ :=
  ⟨fun x _ =>
    match x with
    | .bot => "⊥"
    | .botₚ => "⊥ₚ"
    | .topₚ => "⊤ₚ"
    | .top => "⊤"⟩

-- ------------------------------------------------------------------------------------
-- Pre order for 𝔹₄
-- ------------------------------------------------------------------------------------

def le_𝔹₄ : 𝔹₄ → 𝔹₄ → Prop
  | .bot, _ => True
  | _, .bot => False
  | ⊥ₚ, _ => True
  | _, ⊥ₚ => False
  | ⊤ₚ, _ => True
  | _, ⊤ₚ => False
  | .top, .top => True

notation a "⊆₄" b => le_𝔹₄ a b

instance PreOrder_𝔹₄ : Preorder 𝔹₄ where
  le := le_𝔹₄
  le_refl := by
    intro a; cases a <;> trivial
  le_trans := by
    intros a b c h1 h2; cases a <;> cases b <;> cases c <;> trivial

-- ------------------------------------------------------------------------------------
-- Partial order for 𝔹₄
-- ------------------------------------------------------------------------------------

instance PartialOrder_𝔹₄ : PartialOrder 𝔹₄ where
  __ := PreOrder_𝔹₄
  le_antisymm := by
    intros a b h1 h2; cases a <;> cases b <;> trivial

-- ------------------------------------------------------------------------------------
-- Lattice for 𝔹₄
-- ------------------------------------------------------------------------------------

def join_𝔹₄ : 𝔹₄ → 𝔹₄ → 𝔹₄
  | .bot, p => p
  | p, .bot => p
  | ⊥ₚ, p => p
  | p, ⊥ₚ => p
  | ⊤ₚ, p => p
  | p, ⊤ₚ => p
  | .top, .top => .top

def meet_𝔹₄ : 𝔹₄ → 𝔹₄ → 𝔹₄
  | .top, p => p
  | p, .top => p
  | ⊤ₚ, p => p
  | p, ⊤ₚ => p
  | ⊥ₚ, p => p
  | p, ⊥ₚ => p
  | .bot, .bot => .bot

instance SemilatticeSup_𝔹₄ : SemilatticeSup 𝔹₄ where
  __ := PartialOrder_𝔹₄
  sup := join_𝔹₄
  le_sup_left := by
    intro a b; cases a <;> cases b <;> trivial
  le_sup_right := by
    intro a b; cases a <;> cases b <;> trivial
  sup_le := by
    intro a b c h1 h2; cases a <;> cases b <;> cases c <;> trivial

instance SemilatticeInf_𝔹₄ : SemilatticeInf 𝔹₄ where
  __ := PartialOrder_𝔹₄
  inf := meet_𝔹₄
  inf_le_left := by
    intro a b; cases a <;> cases b <;> trivial
  inf_le_right := by
    intro a b; cases a <;> cases b <;> trivial
  le_inf := by
    intro a b c h1 h2; cases a <;> cases b <;> cases c <;> trivial

instance Lattice_𝔹₄ : Lattice 𝔹₄ where
  __ := SemilatticeSup_𝔹₄
  __ := SemilatticeInf_𝔹₄

-- PartialOrder_𝔹₄ is imported twice ... It should the same

theorem SamePreOrder_𝔹₄ : Lattice_𝔹₄.toPartialOrder = PartialOrder_𝔹₄ := by rfl

-- ------------------------------------------------------------------------------------
-- Boolean Lattice for 𝔹₄
-- ------------------------------------------------------------------------------------

def not_𝔹₄ : 𝔹₄ → 𝔹₄
  | .top => .bot
  | ⊤ₚ => ⊥ₚ
  | ⊥ₚ => ⊤ₚ
  | .bot => .top

instance BoundedOrder_𝔹₄ : BoundedOrder 𝔹₄ where
  bot := .bot
  top := .top
  bot_le := by
    intro a; cases a <;> trivial
  le_top := by
    intro a; cases a <;> trivial

instance BooleanLattice_𝔹₄ : BooleanLattice 𝔹₄ where
  __ := Lattice_𝔹₄
  __ := BoundedOrder_𝔹₄
  compl := not_𝔹₄

-- 𝔹₄ is not a Boolean algebra: `botₚ ⊓ botₚᶜ = botₚ ≠ ⊥` and `botₚ ⊔ botₚᶜ = topₚ ≠ ⊤`.
lemma not_inf_compl_eq_bot₄ : ¬∀ a : 𝔹₄, a ⊓ aᶜ = ⊥ := by
  intro h; cases h ⊥ₚ

lemma not_sup_compl_eq_top₄ : ¬∀ a : 𝔹₄, a ⊔ aᶜ = ⊤ := by
  intro h; cases h ⊥ₚ

instance BooleanLatticeProperties_𝔹₄ : BooleanLatticeProperties 𝔹₄ where
  __ := BooleanLattice_𝔹₄
  commut_cap := by
    intro a b; cases a <;> cases b <;> trivial
  commut_cup := by
    intro a b; cases a <;> cases b <;> trivial
  assoc_cap := by
    intro a b c; cases a <;> cases b <;> cases c <;> trivial
  assoc_cup := by
    intro a b c; cases a <;> cases b <;> cases c <;> trivial
  distr_cap := by
    intro a b c; cases a <;> cases b <;> cases c <;> trivial
  distr_cup := by
    intro a b c; cases a <;> cases b <;> cases c <;> trivial

instance BooleanNegationProperties_𝔹₄ : BooleanNegationProperties 𝔹₄ where
  __ := BooleanLattice_𝔹₄
  not_not := by
    intro a; cases a <;> trivial

@[simp]
lemma compl_compl₄ (a : 𝔹₄) : aᶜᶜ = a := by cases a <;> rfl

@[simp]
lemma compl_sup₄ (a b : 𝔹₄) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by cases a <;> cases b <;> rfl

@[simp]
lemma compl_inf₄ (a b : 𝔹₄) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by cases a <;> cases b <;> rfl

@[simp]
lemma bot_eq₄ : 𝔹₄.bot = ⊥ :=
  rfl

@[simp]
lemma top_eq₄ : 𝔹₄.top = ⊤ :=
  rfl

@[simp]
lemma compl_bot₄ : (⊥ : 𝔹₄)ᶜ = ⊤ :=
  rfl

@[simp]
lemma compl_botₚ : (⊥ₚ)ᶜ = ⊤ₚ :=
  rfl

@[simp]
lemma compl_topₚ : (⊤ₚ)ᶜ = ⊥ₚ :=
  rfl

@[simp]
lemma compl_top₄ : (⊤ : 𝔹₄)ᶜ = ⊥ :=
  rfl

lemma compl_le_compl₄ {a b : 𝔹₄} (h : a ≤ b) : bᶜ ≤ aᶜ := by cases a <;> cases b <;> trivial

-- Join / meet of the two "presumably" values (the other cases are covered by Mathlib)
@[simp]
lemma botₚ_sup_topₚ : ⊥ₚ ⊔ ⊤ₚ = ⊤ₚ :=
  rfl

@[simp]
lemma topₚ_sup_botₚ : ⊤ₚ ⊔ ⊥ₚ = ⊤ₚ :=
  rfl

@[simp]
lemma botₚ_inf_topₚ : ⊥ₚ ⊓ ⊤ₚ = ⊥ₚ :=
  rfl

@[simp]
lemma topₚ_inf_botₚ : ⊤ₚ ⊓ ⊥ₚ = ⊥ₚ :=
  rfl

-- 𝔹₄ is a DeMorgan Algebra:

-- https://ncatlab.org/nlab/show/De+Morgan+algebra
class DeMorganAlgebra (A : Type) extends DistribLattice A, BoundedOrder A, Compl A where
  compl_compl : ∀ a : A, aᶜᶜ = a
  compl_sup : ∀ a b : A, (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ

instance DeMorganAlgebra_𝔹₄ : DeMorganAlgebra 𝔹₄ where
  __ := BooleanLattice_𝔹₄
  le_sup_inf := by
    intro x y z
    rw [BooleanLatticeProperties.distr_cup]
  compl_compl := compl_compl₄
  compl_sup := compl_sup₄

-- ------------------------------------------------------------------------------------
-- Implication for 𝔹₄
-- ------------------------------------------------------------------------------------

-- Semantic Kleene implication
def impl_𝔹₄ (a b : 𝔹₄) : 𝔹₄ :=
  aᶜ ⊔ b

infixr:60 " ⇒ " => impl_𝔹₄

-- Not simp: unfold on demand with `simp [impl_def₄]`, otherwise it hides the lemmas below.
lemma impl_def₄ (a b : 𝔹₄) : (a ⇒ b) = aᶜ ⊔ b :=
  rfl

@[simp]
lemma bot_impl₄ (a : 𝔹₄) : (⊥ ⇒ a) = ⊤ := by cases a <;> rfl

@[simp]
lemma impl_top₄ (a : 𝔹₄) : (a ⇒ ⊤) = ⊤ := by cases a <;> rfl

@[simp]
lemma top_impl₄ (a : 𝔹₄) : (⊤ ⇒ a) = a := by cases a <;> rfl

-- Contraposition (not simp: it would loop)
lemma impl_contra₄ (a b : 𝔹₄) : (a ⇒ b) = (bᶜ ⇒ aᶜ) := by cases a <;> cases b <;> rfl

-- Like the Boolean laws above, `a ⇒ a = ⊤` fails: `botₚ ⇒ botₚ = topₚ`.
lemma not_impl_self₄ : ¬∀ a : 𝔹₄, (a ⇒ a) = ⊤ := by
  intro h; cases h ⊥ₚ

-- `a ⇒ a = ⊤` holds exactly on the definite values ⊥ and ⊤ ...
@[simp]
lemma impl_self_eq_top₄ (a : 𝔹₄) : (a ⇒ a) = ⊤ ↔ a = ⊥ ∨ a = ⊤ := by
  cases a
  · exact iff_of_true rfl (Or.inl rfl)
  · exact iff_of_false (fun h => by cases h) (by rintro (h | h) <;> cases h)
  · exact iff_of_false (fun h => by cases h) (by rintro (h | h) <;> cases h)
  · exact iff_of_true rfl (Or.inr rfl)

@[simp]
lemma topₚ_le_impl_self₄ (a : 𝔹₄) : ⊤ₚ ≤ (a ⇒ a) := by cases a <;> trivial
