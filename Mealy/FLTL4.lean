import Mealy
import Mathlib.Data.Finset.Lattice.Fold
import LeanSearchClient

open TruthDomain.TruthDomain_𝔹₄

namespace FLTL₄

variable (α : Type u) [DecidableEq α]

inductive φ : Type u where
  | true : φ
  | false : φ
  | or : φ → φ → φ
  | and : φ → φ → φ
  | ap : α → φ
  | not : φ → φ
  | next : φ → φ
  | weak_next : φ → φ
  | until : φ → φ → φ
  | release : φ → φ → φ
  | finally : φ → φ
  | globally : φ → φ
  deriving DecidableEq, Repr

-- https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/#variables-and-sections
variable { α }

prefix:60 "~ " => φ.not

infixr:130 " ⋀ " => φ.and

infixr:130 " ⋁ " => φ.or

prefix:75 "𝑿 " => φ.next

prefix:75 "X̅ " => φ.weak_next

infixr:110 " 𝑼 " => φ.until

infixr:110 " 𝑹 " => φ.release

prefix:100 "𝑭 " => φ.finally

prefix:100 "𝑮 " => φ.globally

notation "⟨ " e " ⟩" => φ.ap e

/-
def exampleNat : φ ℕ :=
  (𝑮 (⟨1⟩ 𝑼 ⟨2⟩)) ⋀ (𝑮 (~ ⟨0⟩))

def exampleString : φ String :=
  (𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩))
-/

abbrev lookup (w : List α) (i : ℕ) (x : α) : Bool :=
  w[i]? == .some x

abbrev nlookup (w : List α) (i : ℕ) (x : α) : Bool :=
  (lookup w i x)ᶜ

-- `w |` : for atomic proposition not in a term
syntax :50 (name := nth) term:51 " ∈ " ident "[" term "]" : term

macro_rules (kind := nth)
  | `($x ∈ $w[$i]) => `(lookup $w $i $x)

-- `w |` : for atomic proposition in a term
syntax :50 (name := notNth) term:51 " ∉ " ident "[" term "]" : term

macro_rules (kind := notNth)
  | `($x ∉ $w[$i]) => `(nlookup $w $i $x)

-- `| w |` : for list cardinality
syntax :100 (name := card) "| " term " |" : term

macro_rules (kind := card)
  | `(| $w |) => `(List.length $w)

-- `⨆ i ∈ w, f i` : join of `f i` over the positions `i` of `w`
syntax :67 (name := supPos) "⨆ " ident " ∈ " term ", " term : term

macro_rules (kind := supPos)
  | `(⨆ $i:ident ∈ $w, $f) => `((Finset.range $w).sup fun $i => $f)

-- ``⨅ i ∈ w, f i` : meet of `f i` over the positions `i` of `w`
syntax :67 (name := infPos) "⨅ " ident " ∈ " term ", " term : term

macro_rules (kind := infPos)
  | `(⨅ $i:ident ∈ $w, $f) => `((Finset.range $w).inf fun $i => $f)

set_option hygiene false in
notation:200 "⟦ " w " ⊨ " p " ⟧₄" => sem w p

def sem (w : List α) : φ α → 𝔹₄
  | .true => .top
  | .false => .bot
  | φ ⋁ ψ => ⟦ w ⊨ φ ⟧₄ ⊔ ⟦ w ⊨ ψ ⟧₄
  | φ ⋀ ψ => ⟦ w ⊨ φ ⟧₄ ⊓ ⟦ w ⊨ ψ ⟧₄
  | ⟨x⟩ => if x ∈ w[0] then .top else .bot
  | ~ ⟨x⟩ => if x ∉ w[0] then .top else .bot
  | ~ φ => (⟦ w ⊨ φ ⟧₄)ᶜ
  | 𝑿 φ => if | w | > 1 then ⟦ w.drop 1 ⊨ φ ⟧₄ else .botₚ
  | X̅ φ => if | w | > 1 then ⟦ w.drop 1 ⊨ φ ⟧₄ else .topₚ
  | 𝑮 φ => .botₚ ⊔ (⨆ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧₄)
  | 𝑭 φ => .topₚ ⊓ (⨅ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧₄)
  | φ 𝑼 ψ =>
    (⨆ i ∈ | w |, ⟦ w.drop i ⊨ ψ ⟧₄ ⊓ (⨅ j ∈ i, ⟦ w.drop j ⊨ φ ⟧₄)) ⊔
      (.botₚ ⊓ (⨆ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧₄))
  | φ 𝑹 ψ =>
    (⨆ i ∈ | w |, ⟦ w.drop i ⊨ ψ ⟧₄ ⊓ (⨅ j ∈ i, ⟦ w.drop j ⊨ φ ⟧₄)) ⊔
      (.topₚ ⊓ (⨆ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧₄))

-- Associativity for ⋁ and ⋀

-- https://lean-lang.org/doc/reference/4.33.0/Tactic-Proofs/Tactic-Reference/

theorem or_associativity: ∀ (w: List α), ∀ (a b c: φ α), ⟦ w ⊨ a ⋁ (b ⋁ c) ⟧₄ = ⟦ w ⊨ (a ⋁ b) ⋁ c ⟧₄ := by
  intro w a b c
  simp [sem]
  rw [BooleanLatticeProperties_𝔹₄.assoc_cup]

theorem and_associativity: ∀ (w: List α), ∀ (a b c: φ α), ⟦ w ⊨ a ⋀ (b ⋀ c) ⟧₄ = ⟦ w ⊨ (a ⋀ b) ⋀ c ⟧₄ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.assoc_cap _ _ _
  -- exact BooleanLatticeProperties_𝔹₄.assoc_cap .. where .. interpolates metavariable
