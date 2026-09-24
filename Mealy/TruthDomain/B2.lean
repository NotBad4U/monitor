import Mealy.TruthDomain.Core

-- ====================================================================================
-- 𝔹₂
-- ====================================================================================

inductive 𝔹₂ where
  | bot
  | top

deriving instance BEq, Hashable for 𝔹₂

-- ------------------------------------------------------------------------------------
-- Pre order for 𝔹₂
-- ------------------------------------------------------------------------------------

def le_𝔹₂ : 𝔹₂ → 𝔹₂ → Prop
  | .top, .bot => False
  | _, _ => True

notation a "⊆₂" b => le_𝔹₂ a b

instance PreOrder_𝔹₂ : Preorder 𝔹₂ where
  le := le_𝔹₂
  le_refl := by
    intro a; cases a <;> trivial
  le_trans := by
    intros a b c h1 h2; cases a <;> cases b <;> cases c <;> trivial

-- ------------------------------------------------------------------------------------
-- Partial order for 𝔹₂
-- ------------------------------------------------------------------------------------

instance PartialOrder_𝔹₂ : PartialOrder 𝔹₂ where
  __ := PreOrder_𝔹₂
  le_antisymm := by
    intros a b h1 h2; cases a <;> cases b <;> trivial

-- ------------------------------------------------------------------------------------
-- Lattice for 𝔹₂
-- ------------------------------------------------------------------------------------

def join_𝔹₂ : 𝔹₂ → 𝔹₂ → 𝔹₂
  | .bot, .bot => .bot
  | _, _ => .top

def meet_𝔹₂ : 𝔹₂ → 𝔹₂ → 𝔹₂
  | .top, .top => .top
  | _, _ => .bot

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html#Lattices

instance SemilatticeSup_𝔹₂ : SemilatticeSup 𝔹₂ where
  __ := PartialOrder_𝔹₂
  sup := join_𝔹₂
  le_sup_left := by
    intro a b; cases a <;> cases b <;> trivial
  le_sup_right := by
    intro a b; cases a <;> cases b <;> trivial
  sup_le := by
    intro a b c h1 h2; cases a <;> cases b <;> cases c <;> trivial

instance SemilatticeInf_𝔹₂ : SemilatticeInf 𝔹₂ where
  __ := PartialOrder_𝔹₂
  inf := meet_𝔹₂
  inf_le_left := by
    intro a b; cases a <;> cases b <;> trivial
  inf_le_right := by
    intro a b; cases a <;> cases b <;> trivial
  le_inf := by
    intro a b c h1 h2; cases a <;> cases b <;> cases c <;> trivial

instance Lattice_𝔹₂ : Lattice 𝔹₂ where
  __ := SemilatticeSup_𝔹₂
  __ := SemilatticeInf_𝔹₂

-- PartialOrder_𝔹₂ is imported twice ... It should the same

theorem SamePreOrder_𝔹₂ : Lattice_𝔹₂.toPartialOrder = PartialOrder_𝔹₂ := by rfl

-- ------------------------------------------------------------------------------------
-- Boolean Lattice for 𝔹₂
-- ------------------------------------------------------------------------------------

def not_𝔹₂ : 𝔹₂ → 𝔹₂
  | .top => .bot
  | .bot => .top

instance BoundedOrder_𝔹₂ : BoundedOrder 𝔹₂ where
  bot := .bot
  top := .top
  bot_le := by
    intro a; cases a <;> trivial
  le_top := by
    intro a; cases a <;> trivial

instance BooleanLattice_𝔹₂ : BooleanLattice 𝔹₂ where
  __ := Lattice_𝔹₂
  __ := BoundedOrder_𝔹₂
  compl := not_𝔹₂

instance BooleanLatticeProperties_𝔹₂ : BooleanLatticeProperties 𝔹₂ where
  __ := BooleanLattice_𝔹₂
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

instance BooleanNegationProperties_𝔹₂ : BooleanNegationProperties 𝔹₂ where
  __ := BooleanLattice_𝔹₂
  not_not := by
    intro a; cases a <;> trivial
