import Mathlib.Order.Defs.PartialOrder -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html

-- https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/
namespace TruthDomain

class BooleanLattice (A: Type) [PartialOrder A] where
  bot: A
  top: A
  cup: A → A → A
  cap: A → A → A

infixl:65 " ⊔ " => BooleanLattice.cup
infixl:70 " ⊓ " => BooleanLattice.cap

class BooleanLatticeProperties (A: Type) [PartialOrder A] extends BooleanLattice A where
  distr_cap : ∀ a b c : A, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
  distr_cup : ∀ a b c : A, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)

-- Boolean 2
inductive 𝔹₂ where
  | bot
  | top
deriving instance BEq, Hashable for 𝔹₂

def le_𝔹₂ : 𝔹₂ → 𝔹₂ → Prop
  | .top, .bot => False
  | _, _ => True

def join : 𝔹₂ → 𝔹₂ → 𝔹₂
  | .bot, .bot => .bot
  | _, _ => .top

def meet : 𝔹₂ → 𝔹₂ → 𝔹₂
  | .top, .top => .top
  | _, _ => .bot

-- instance [PartialOrder α] : Std.IsPartialOrder α where
--   le_antisymm := PartialOrder.le_antisymm

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Cases.html

instance PartialOrder𝔹₂: PartialOrder 𝔹₂ where
  le := le_𝔹₂
  le_refl := by
    intro a <;> cases a <;> trivial
  le_trans:= by
    intros a b c h1 h2 <;> cases a <;> cases b <;> cases c <;> trivial
  le_antisymm := by
    intros a b h1 h2 <;> cases a <;> cases b <;> trivial

inductive 𝔹₄ where
  | bot
  | botₚ
  | topₚ
  | top
deriving instance BEq, Hashable for 𝔹₄

def le_𝔹₄ : 𝔹₄ → 𝔹₄ → Prop
  | .bot, _ => True
  | .botₚ, .bot => False
  | .botₚ, _ => True
  | .topₚ, .bot => False
  | .topₚ, .botₚ => False
  | .topₚ, _ => True
  | .top, .top => True
  | .top, _ => False

notation a "≤₄" b => le_𝔹₄ a b

instance PartialOrder𝔹₄: PartialOrder 𝔹₄ where
  le := le_𝔹₄
  
  le_refl := by intro a <;> cases a <;> trivial
  le_trans:= by
    intros a b c h1 h2 <;> cases a <;> cases b <;> cases c <;> trivial
  le_antisymm := by
    intros a b h1 h2 <;> cases a <;> cases b <;> trivial

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html#Lattices
