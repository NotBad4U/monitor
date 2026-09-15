import Mathlib.Order.Defs.PartialOrder -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html
import Mathlib.Order.Lattice -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html

-- https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/

namespace TruthDomain

class BooleanLattice (A: Type) [PartialOrder A] where
  bot: A
  top: A
  cup: A → A → A
  cap: A → A → A

infixl:65 "⊔" => BooleanLattice.cup
infixl:70 "⊓" => BooleanLattice.cap

class BooleanLatticeProperties (A: Type) [PartialOrder A] extends BooleanLattice A where
  distr_cap : ∀ a b c : A, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
  distr_cup : ∀ a b c : A, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)

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

instance PreOrder_𝔹₂: Preorder 𝔹₂ where
  le := le_𝔹₂
  le_refl := by intro a ; cases a <;> trivial
  le_trans := by intros a b c h1 h2 ; cases a <;> cases b <;> cases c <;> trivial

-- ------------------------------------------------------------------------------------
-- Partial order for 𝔹₂
-- ------------------------------------------------------------------------------------

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Cases.html
instance PartialOrder_𝔹₂: PartialOrder 𝔹₂ where
  __ := PreOrder_𝔹₂
  le_antisymm := by intros a b h1 h2 ; cases a <;> cases b <;> trivial

-- ------------------------------------------------------------------------------------
-- Semi Lattice for 𝔹₂
-- ------------------------------------------------------------------------------------

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html#Lattices

def join_𝔹₂ : 𝔹₂ → 𝔹₂ → 𝔹₂
  | .bot, .bot => .bot
  | _, _ => .top

def meet_𝔹₂ : 𝔹₂ → 𝔹₂ → 𝔹₂
  | .top, .top => .top
  | _, _ => .bot

instance SemilatticeSup_𝔹₂ : SemilatticeSup 𝔹₂ where
  __ := PartialOrder_𝔹₂
  sup := join_𝔹₂
  le_sup_left  := by intro a b ; cases a <;> cases b <;> trivial
  le_sup_right := by intro a b ; cases a <;> cases b <;> trivial
  sup_le       := by intro a b c h1 h2 ; cases a <;> cases b <;> cases c <;> trivial

instance SemilatticeInf_𝔹₂ : SemilatticeInf 𝔹₂ where
  __ := PartialOrder_𝔹₂
  inf := meet_𝔹₂
  inf_le_left  := by intro a b ; cases a <;> cases b <;> trivial
  inf_le_right := by intro a b ; cases a <;> cases b <;> trivial
  le_inf       := by intro a b c h1 h2 ; cases a <;> cases b <;> cases c <;> trivial

instance Lattice_𝔹₂ : Lattice 𝔹₂ where
  __ := SemilatticeInf_𝔹₂
  __ := SemilatticeSup_𝔹₂

-- ====================================================================================
-- 𝔹₄
-- ====================================================================================

inductive 𝔹₄ where
  | bot
  | botₚ
  | topₚ
  | top
deriving instance BEq, Hashable for 𝔹₄

-- ------------------------------------------------------------------------------------
-- Pre order for 𝔹₂
-- ------------------------------------------------------------------------------------

def le_𝔹₄ : 𝔹₄ → 𝔹₄ → Prop
  | .bot, _ => True
  | _, .bot => False
  | .botₚ, _ => True
  | _, .botₚ => False
  | .topₚ, _ => True
  | _, .topₚ  => False
  | .top, .top => True

notation a "⊆₄" b => le_𝔹₄ a b

instance PreOrder_𝔹₄: Preorder 𝔹₄ where
  le := le_𝔹₄
  le_refl := by intro a ; cases a <;> trivial
  le_trans := by intros a b c h1 h2 ; cases a <;> cases b <;> cases c <;> trivial

-- ------------------------------------------------------------------------------------
-- Partial order for 𝔹₄
-- ------------------------------------------------------------------------------------

instance PartialOrder_𝔹₄: PartialOrder 𝔹₄ where
  __ := PreOrder_𝔹₄
  le_antisymm := by intros a b h1 h2 ; cases a <;> cases b <;> trivial

-- ------------------------------------------------------------------------------------
-- Semi Lattice for 𝔹₄
-- ------------------------------------------------------------------------------------

def join_𝔹₄ : 𝔹₄ → 𝔹₄ → 𝔹₄
  | .bot, p => p
  | p, .bot => p
  | .botₚ, p => p
  | p, .botₚ => p
  | .topₚ, p => p
  | p, .topₚ => p
  | .top, .top => .top

def meet_𝔹₄ : 𝔹₄ → 𝔹₄ → 𝔹₄
  | .top, p => p
  | p, .top => p
  | .topₚ, p => p
  | p, .topₚ => p
  | .botₚ, p => p
  | p, .botₚ => p
  | .bot, .bot => .bot

instance SemilatticeSup_𝔹₄ : SemilatticeSup 𝔹₄ where
  __ := PartialOrder_𝔹₄
  sup := join_𝔹₄
  le_sup_left  := by intro a b ; cases a <;> cases b <;> trivial
  le_sup_right := by intro a b ; cases a <;> cases b <;> trivial
  sup_le       := by intro a b c h1 h2 ; cases a <;> cases b <;> cases c <;> trivial

instance SemilatticeInf_𝔹₄ : SemilatticeInf 𝔹₄ where
  __ := PartialOrder_𝔹₄
  inf := meet_𝔹₄
  inf_le_left  := by intro a b ; cases a <;> cases b <;> trivial
  inf_le_right := by intro a b ; cases a <;> cases b <;> trivial
  le_inf       := by intro a b c h1 h2 ; cases a <;> cases b <;> cases c <;> trivial

instance Lattice_𝔹₄ : Lattice 𝔹₄ where
  __ := SemilatticeInf_𝔹₄
  __ := SemilatticeSup_𝔹₄

-- ====================================================================================
-- End of File
-- ====================================================================================
