import Mealy.TruthDomain
import Mathlib.Data.Finset.Lattice.Fold
import LeanSearchClient

open TruthDomain.TruthDomain_𝔹₄

namespace FLTL₄

variable (α : Type u) [DecidableEq α]

inductive φ : Type (u + 1) where
  | true : φ
  | false : φ
  | ap : α → φ
  | not : φ → φ
  | and : φ → φ → φ
  | or : φ → φ → φ
  | next : φ → φ
  | until : φ → φ → φ
  | weak_next : φ → φ
  | release : φ → φ → φ
  | finally : φ → φ
  | globally : φ → φ
  deriving DecidableEq, Repr

variable {α}

prefix:60 "~ " => φ.not

infixr:130 " ⋀ " => φ.and

infixr:130 " ⋁ " => φ.or

prefix:75 "𝑿 " => φ.next

prefix:75 "X̅ " => φ.weak_next -- Je n'arrive pas à combiner \MIX et \overline ou \bar

infixr:110 " 𝑼 " => φ.until

infixr:110 " 𝑹 " => φ.release

prefix:100 "𝑭 " => φ.finally

prefix:100 "𝑮 " => φ.globally

notation "⟨ " e " ⟩" => φ.ap e

notation " ⊤ " => φ.true

notation " ⊥ " => φ.false

-- Implication as a derived connective: a ⟶ b := ~a ⋁ b
abbrev φ.impl (a b : φ α) : φ α :=
  (~ a) ⋁ b

infixr:105 " ⟶ " => φ.impl

def exampleNat : φ ℕ :=
  (𝑮 (⟨ 1 ⟩ 𝑼 ⟨ 2 ⟩)) ⋀ (𝑮 (~ ⟨ 0 ⟩))

def exampleString : φ String :=
  (𝑮 (⟨ "a" ⟩ 𝑼 ⟨ "b" ⟩)) ⋀ (𝑮 (~ ⟨ "c" ⟩))

-- Put a formula φ into a Negation Normal Form i.e negation on the leaves
def nnf : φ α → φ α
  | ~ ⊤ => ⊥
  | ~ ⊥ => ⊤
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
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ⟨ x ⟩ => ⟨ x ⟩

-- Decidable predicate to check if a formula φ is in Negation Normal Form
def is_nnf : φ α → Bool
  | ~ ⊤ => false -- ~ ⊤ => ⊥
  | ~ ⊥ => false -- ~ ⊥ => ⊤
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
  | ⊤ => true
  | ⊥ => true
  | ⟨ _ ⟩ => true

-- `nnf` always produces a formula in negation normal form
omit [DecidableEq α] in -- Recommended by Lean
theorem nnf_is_nnf (f : φ α) : is_nnf (nnf f) = true := by
  induction f using nnf.induct <;> simp_all [nnf, is_nnf]

set_option hygiene false in
notation:200 "⟦ " w " ⊨ " p " ⟧" => sem w p

abbrev lookup (w : List α) (i : ℕ) (x : α) : 𝔹₄ :=
  if w[i - 1]? = .some x then .top else .bot

abbrev nlookup (w : List α) (i : ℕ) (x : α) : 𝔹₄ :=
  if w[i - 1]? = .some x then .bot else .top

@[simp]
lemma compl_lookup (w : List α) (i : ℕ) (x : α) : (lookup w i x)ᶜ = nlookup w i x := by
  unfold lookup nlookup; split <;> rfl

syntax :50 (name := memAt) term:51 " ∈ " ident "[" term "]" : term

macro_rules (kind := memAt)
  | `($x ∈ $w:ident[$i]) => `(lookup $w $i $x)

syntax :50 (name := notMemAt) term:51 " ∉ " ident "[" term "]" : term

macro_rules (kind := notMemAt)
  | `($x ∉ $w:ident[$i]) => `(nlookup $w $i $x)

-- `| w |` : join / meet of `f i` over the positions `i` of `w`
syntax :67 (name := card) "| " term " |" : term

macro_rules (kind := card)
  | `(| $w:ident |) => `(List.length $w)

-- `⨆ i ∈ w, f i` : join of `f i` over the positions `i` of `w`
syntax :67 (name := supPos) "⨆ " ident " ∈ " term ", " term : term

macro_rules (kind := supPos)
  | `(⨆ $i:ident ∈ $w:term, $f) => `((Finset.range $w).sup fun $i => $f)

-- ``⨅ i ∈ w, f i` : meet of `f i` over the positions `i` of `w`
syntax :67 (name := infPos) "⨅ " ident " ∈ " term ", " term : term

macro_rules (kind := infPos)
  | `(⨅ $i:ident ∈ $w:term, $f) => `((Finset.range $w).inf fun $i => $f)

def sem (w : List α) : φ α → 𝔹₄
  | ⊤ => .top
  | ⊥ => .bot
  | ~ ⟨ x ⟩ => x ∉ w[0]
  | ⟨ x ⟩ => x ∈ w[0]
  | ~ φ => (⟦ w ⊨ φ ⟧)ᶜ
  | φ ⋁ ψ => ⟦ w ⊨ φ ⟧ ⊔ ⟦ w ⊨ ψ ⟧
  | φ ⋀ ψ => ⟦ w ⊨ φ ⟧ ⊓ ⟦ w ⊨ ψ ⟧
  | 𝑿 φ => if | w | > 0 then ⟦ w.tail ⊨ φ ⟧ else .botₚ
  | X̅ φ => if | w | > 0 then ⟦ w.tail ⊨ φ ⟧ else .topₚ
  | 𝑮 φ => .botₚ ⊔ (⨆ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧)
  | 𝑭 φ => .topₚ ⊓ (⨅ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧)
  | φ 𝑼 ψ =>
    (⨆ i ∈ | w |, (⟦ w.drop i ⊨ ψ ⟧ ⊓ (⨅ j ∈ i, ⟦ w.drop j ⊨ φ ⟧))) ⊔
      (.botₚ ⊓ (⨆ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧))
  | φ 𝑹 ψ =>
    (⨅ i ∈ | w |, (⟦ w.drop i ⊨ ψ ⟧ ⊔ (⨆ j ∈ i, ⟦ w.drop j ⊨ φ ⟧))) ⊓
      (.topₚ ⊔ (⨅ i ∈ | w |, ⟦ w.drop i ⊨ φ ⟧))

-- https://lean-lang.org/doc/reference/4.33.0/Tactic-Proofs/Tactic-Reference/

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

@[simp]
lemma compl_range_sup (n : ℕ) (f : ℕ → 𝔹₄) :
    ((Finset.range n).sup f)ᶜ = (Finset.range n).inf (fun i => (f i)ᶜ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finset.range_add_one, ih]

@[simp]
lemma compl_range_inf (n : ℕ) (f : ℕ → 𝔹₄) :
    ((Finset.range n).inf f)ᶜ = (Finset.range n).sup (fun i => (f i)ᶜ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finset.range_add_one, ih]

@[simp]
lemma compl_ite₄ (c : Prop) [Decidable c] (a b : 𝔹₄) :
    (if c then a else b)ᶜ = if c then aᶜ else bᶜ := by split <;> rfl

@[simp]
lemma sem_not (w : List α) (f : φ α) : ⟦ w ⊨ ~ f ⟧ = (⟦ w ⊨ f ⟧)ᶜ := by
  cases f with
  | ap x => simp [sem, nlookup]
  | _ => simp [sem]

theorem sem_nnf_equiv (w : List α) (f : φ α) : ⟦ w ⊨ nnf f ⟧ = ⟦ w ⊨ f ⟧ := by
  induction f using nnf.induct generalizing w <;> simp_all [nnf, sem, nlookup]

omit [DecidableEq α] in
lemma nnf_impl (a b : φ α) : nnf (a ⟶ b) = nnf (~ a) ⋁ nnf b := by simp [nnf]

lemma sem_impl (w : List α) (a b : φ α) : ⟦ w ⊨ a ⟶ b ⟧ = (⟦ w ⊨ a ⟧ ⇒ ⟦ w ⊨ b ⟧) := by
  simp [sem, impl_def₄]

-- https://en.wikipedia.org/wiki/Modal_logic

-- K i.e. arbitrary Kripke frame : □ (a → b) ⊢ □ a → □ b
lemma sem_frame (w : List α) (a b : φ α) : ⟦ w ⊨ 𝑮 (a ⟶ b) ⟧ ≤ ⟦ w ⊨ (𝑮 a) ⟶ (𝑮 b) ⟧ := by sorry

-- 4 i.e transitivitt : □p ⊢ □□p
lemma sem_transitivity_G (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑮 f ⟧ := by sorry

-- T i.e. reflexivity □p ⊢ p
lemma sem_reflexivity_G (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ f ⟧ := by sorry

-- B i.e. symmetry p ⊢ □♢p
lemma sem_symmetry (w : List α) (f : φ α) : ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ := by sorry

-- 5 i.e euclideanity  ♢p → ◻◊p
lemma sem_euclideanity (w : List α) (f : φ α) : ⟦ w ⊨ 𝑭 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ := by sorry
