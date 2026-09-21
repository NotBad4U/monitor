import Mealy.TruthDomain
import Mathlib.Data.Finset.Lattice.Fold
import LeanSearchClient

open TruthDomain.TruthDomain_𝔹₄

-- uncomment for dev mode only
set_option pp.parens true

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

-- `⨆ i < n, f i` : join of `f i` over the indices `i < n`
syntax :67 (name := supLt) "⨆ " ident " < " term ", " term : term

macro_rules (kind := supLt)
  | `(⨆ $i:ident < $n:term, $f) => `((Finset.range $n).sup fun $i => $f)

-- `⨅ i < n, f i` : meet of `f i` over the indices `i < n`
syntax :67 (name := infLt) "⨅ " ident " < " term ", " term : term

macro_rules (kind := infLt)
  | `(⨅ $i:ident < $n:term, $f) => `((Finset.range $n).inf fun $i => $f)

-- `⨆< n, f` / `⨅< n, f` : same, point-free (the family `f` is a function, no binder)
syntax :67 (name := supRange) "⨆< " term:68 ", " term:68 : term

macro_rules (kind := supRange)
  | `(⨆< $n, $f) => `((Finset.range $n).sup $f)

syntax :67 (name := infRange) "⨅< " term:68 ", " term:68 : term

macro_rules (kind := infRange)
  | `(⨅< $n, $f) => `((Finset.range $n).inf $f)

-- `syntax` + `macro_rules` only expands on input; these unexpanders print the goal back
-- with the notation in the InfoView
@[app_unexpander Finset.sup]
def unexpandRangeSup : Lean.PrettyPrinter.Unexpander
  | `($_ $s fun $i:ident => $f) => do
      match s with
      | `(Finset.range $n) => `(⨆ $i:ident < $n, $f)
      | _ => throw ()
  | `($_ $s $f) => do
      match s with
      | `(Finset.range $n) => `(⨆< $n, $f)
      | _ => throw ()
  | _ => throw ()

@[app_unexpander Finset.inf]
def unexpandRangeInf : Lean.PrettyPrinter.Unexpander
  | `($_ $s fun $i:ident => $f) => do
      match s with
      | `(Finset.range $n) => `(⨅ $i:ident < $n, $f)
      | _ => throw ()
  | `($_ $s $f) => do
      match s with
      | `(Finset.range $n) => `(⨅< $n, $f)
      | _ => throw ()
  | _ => throw ()

-- ``⨅ i ∈ w, f i` : meet of `f i` over the positions `i` of `w`
syntax:75 (name := drop) ident "^" term:76 : term

macro_rules (kind := drop)
  | `($w:ident ^ $i:term) => `(List.drop $i $w)

def sem (w : List α) : φ α → 𝔹₄
  | ⊤ => .top
  | ⊥ => .bot
  | ~ ⟨ x ⟩ => x ∉ w[0]
  | ⟨ x ⟩ => x ∈ w[0]
  | ~ φ => (⟦ w ⊨ φ ⟧)ᶜ
  | φ ⋁ ψ => ⟦ w ⊨ φ ⟧ ⊔ ⟦ w ⊨ ψ ⟧
  | φ ⋀ ψ => ⟦ w ⊨ φ ⟧ ⊓ ⟦ w ⊨ ψ ⟧
  | 𝑿 φ => if | w | > 0 then ⟦ w ^ 1 ⊨ φ ⟧ else ⊥ₚ
  | X̅ φ => if | w | > 0 then ⟦ w ^ 1 ⊨ φ ⟧ else ⊤ₚ
  | 𝑮 φ => ⊤ₚ ⊓ (⨅ i ∈ | w |, ⟦ w ^ i ⊨ φ ⟧)
  | 𝑭 φ => ⊥ₚ ⊔ (⨆ i ∈ | w |, ⟦ w ^ i ⊨ φ ⟧)
  | φ 𝑼 ψ =>
    (⨆ i ∈ | w |, (⟦ w ^ i ⊨ ψ ⟧ ⊓ (⨅ j ∈ i, ⟦ w ^ j ⊨ φ ⟧))) ⊔
      (⊥ₚ ⊓ (⨅ i ∈ | w |, ⟦ w ^ i ⊨ φ ⟧))
  | φ 𝑹 ψ =>
    (⨅ i ∈ | w |, (⟦ w ^ i ⊨ ψ ⟧ ⊔ (⨆ j ∈ i, ⟦ w ^ j ⊨ φ ⟧))) ⊓
      (⊤ₚ ⊔ (⨆ i ∈ | w |, ⟦ w ^ i ⊨ φ ⟧))

-- https://lean-lang.org/doc/reference/4.33.0/Tactic-Proofs/Tactic-Reference/

@[simp]
lemma sem_not_eq_compl_sem (w : List α) (f : φ α) : ⟦ w ⊨ ~ f ⟧ = (⟦ w ⊨ f ⟧)ᶜ := by
  cases f with
  | ap x => simp [sem, nlookup]
  | _ => simp [sem]

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
lemma inf_top_eq_top (i : ℕ) : (⨅ _j < i, 𝔹₄.top) = 𝔹₄.top := Finset.inf_top _

@[simp]
lemma sup_top_eq_top (i : ℕ) (hi : 0 < i) : (⨆ _j < i, 𝔹₄.top) = 𝔹₄.top := by
  apply Finset.sup_const
  exact ⟨0, Finset.mem_range.mpr hi⟩

@[simp]
lemma sup_bot_eq_bot (i : ℕ) : (⨆ _j < i, 𝔹₄.bot) = 𝔹₄.bot := Finset.sup_bot _

@[simp]
lemma inf_bot_eq_bot (i : ℕ) (hi : 0 < i) : (⨅ _j < i, 𝔹₄.bot) = 𝔹₄.bot := by
  apply Finset.inf_const
  exact ⟨0, Finset.mem_range.mpr hi⟩

@[simp]
lemma compl_range_sup (n : ℕ) (f : ℕ → 𝔹₄) :
    (⨆ i ∈ n, f i)ᶜ = (⨅ i ∈ n, (f i)ᶜ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finset.range_add_one, ih]

@[simp]
lemma compl_range_inf (n : ℕ) (f : ℕ → 𝔹₄) :
    (⨅ i ∈ n, f i)ᶜ = (⨆ i ∈ n, (f i)ᶜ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finset.range_add_one, ih]

-- Semantic equivalence between 𝑭𝜑 and true 𝐔 𝜑
lemma eq_sem_F_with_U (w: List α ) (f: φ α) : ⟦ w ⊨ 𝑭 f ⟧ = ⟦ w ⊨ .true 𝑼 f ⟧ := by
   simp only [sem]
   simp only [inf_top_eq_top]
   simp [sup_comm]

-- Semantic equivalence between 𝑮𝜑 and false 𝑹 ϕ
lemma eq_sem_G_with_R (w: List α ) (f: φ α) : ⟦ w ⊨ 𝑮 f ⟧ = ⟦ w ⊨ .false 𝑹 f ⟧ := by
  simp only [sem]
  simp [inf_comm]

-- Semantic equivalence between 𝑮𝜑 and ¬𝑭¬𝜑
lemma equiv_G (w: List α ) (f: φ α) : ⟦ w ⊨ 𝑮 f ⟧ = ⟦ w ⊨ ~ 𝑭 (~ f) ⟧ := by
  simp only [sem]
  simp only [sem_not_eq_compl_sem]
  simp [compl_range_sup]

@[simp]
lemma compl_ite₄ (c : Prop) [Decidable c] (a b : 𝔹₄) :
    (if c then a else b)ᶜ = if c then aᶜ else bᶜ := by split <;> rfl

theorem sem_nnf_equiv (w : List α) (f : φ α) : ⟦ w ⊨ nnf f ⟧ = ⟦ w ⊨ f ⟧ := by
  induction f using nnf.induct generalizing w <;> simp_all [nnf, sem, nlookup]

omit [DecidableEq α] in
lemma nnf_impl (a b : φ α) : nnf (a ⟶ b) = nnf (~ a) ⋁ nnf b := by simp [nnf]

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
  set n := | w |
  set A := fun i => ⟦ w ^ i ⊨ a ⟧ with hA
  set B := fun i => ⟦ w ^ i ⊨ b ⟧ with hB
  show ⊤ₚ ⊓ (⨅ i < n, ((A i)ᶜ ⊔ B i))
        ≤ (⊤ₚ ⊓ (⨅ i < n, A i))ᶜ ⊔ (⊤ₚ ⊓ (⨅ i < n, B i))
  simp_rw [BooleanLatticeProperties_𝔹₄.distr_cup]
  simp
  simp_rw [← BooleanLatticeProperties_𝔹₄.assoc_cup, ← compl_range_inf]
  calc
    ⊤ₚ ⊓ (⨅ i < n, ((A i)ᶜ ⊔ B i)) ≤ ⨅ i < n, ((A i)ᶜ ⊔ B i) := inf_le_right
    _ ≤ (⨆ i < n, (A i)ᶜ) ⊔ (⨅ i < n, B i) := inf_join_le_join_sup_inf n (fun i => (A i)ᶜ) B
    _ = (⨅< n, A)ᶜ ⊔ (⨅ i < n, B i) := by rw [compl_range_inf]
    _ ≤ ⊥ₚ ⊔ ((⨅< n, A)ᶜ ⊔ (⨅ i < n, B i)) := le_sup_right

lemma split_const_left_inf(m : ℕ) (g : ℕ → 𝔹₄) (c : 𝔹₄) :
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
  set n := | w |
  rw [split_const_left_inf]
  refine le_inf inf_le_left (le_inf (le_trans inf_le_left Finset.le_inf_const) ?_)
  refine Finset.le_inf fun i hi => Finset.le_inf fun j hj => ?_
  rw [List.drop_drop]
  refine le_trans inf_le_right (Finset.inf_le ?_)
  simp only [Finset.mem_range, List.length_drop] at *
  lia

-- T i.e. reflexivity □p ⊢ p
theorem sem_reflexivity_G (w : List α) (hw : 0 < | w |) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ f ⟧ := by
  simp only [sem]
  calc
    ⊤ₚ ⊓ (⨅ i < |w|, ⟦ w ^ i ⊨ f ⟧)
        ≤ ⨅ i < |w|, ⟦ w^ i ⊨ f ⟧       := inf_le_right
    _   ≤ ⟦ w ^ 0 ⊨ f ⟧                  := Finset.inf_le (Finset.mem_range.mpr hw)
    _   = ⟦ w ⊨ f ⟧                      := by rw [List.drop_zero]

-- 𝑮 p will never be greather than ⊤ by design of sem
lemma sem_G_le_topₚ (w : List α) (g : φ α) : ⟦ w ⊨ 𝑮 g ⟧ ≤ ⊤ₚ := inf_le_left

-- 𝑭 p will always be greather than ⊥ₚ by design of sem
lemma sem_F_le_botₚ (w : List α) (g : φ α) : ⊥ₚ ≤ ⟦ w ⊨ 𝑭 g ⟧ := le_sup_left

-- 𝑮 p will never be ⊤ by design of sem
lemma sem_G_neq_top (w : List α) (g : φ α) : ⟦ w ⊨ 𝑮 g ⟧ ≠ 𝔹₄.top := by
  simp only [sem]
  intro h
  rw [top_eq₄, inf_eq_top_iff] at h
  exact 𝔹₄.noConfusion h.1


-- 𝑭 p will never be ⊥ by design of sem
lemma sem_F_neq_bot (w : List α) (g : φ α) : ⊥ₚ ≤ ⟦ w ⊨ 𝑭 g ⟧ := le_sup_left

-- 𝑮 is monotone along suffixes i.e. 𝑮 truth value can only get better
lemma sem_G_le_G_drop (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ^ 1 ⊨ 𝑮 f ⟧ := by
  simp only [sem]
  refine le_inf inf_le_left (le_trans inf_le_right (Finset.le_inf fun i hi => ?_))
  rw [List.drop_drop]
  refine Finset.inf_le ?_
  simp only [Finset.mem_range, List.length_drop] at *
  lia

--  𝑭 is antitone along suffixes i.e. 𝑭 truth value can only get worse as time passes;
lemma sem_F_drop_le_F (w : List α) (f : φ α) : ⟦ w ^ 1 ⊨ 𝑭 f ⟧ ≤ ⟦ w ⊨ 𝑭 f ⟧ := by
  simp only [sem]
  refine sup_le_sup_left (Finset.sup_le fun i hi => ?_) _
  rw [List.drop_drop]
  refine Finset.le_sup (f := fun j => ⟦ w^j ⊨ f ⟧) ?_
  simp only [Finset.mem_range, List.length_drop] at *
  lia


#reduce ⟦ [0,1] ⊨ ⟨ 0 ⟩ ⟧
#reduce ⟦ [0,1] ⊨ 𝑮 𝑭 ⟨ 0 ⟩ ⟧

-- B i.e. symmetry p ⊢ □♢p : does NOT hold
-- Witness: w = [0, 1] and f = ⟨0⟩, where ⟦ w ⊨ f ⟧ = ⊤ but ⟦ w ⊨ 𝑮 𝑭 f ⟧ = ⊥ₚ.
theorem not_sem_symmetry : ¬ ∀ (w : List ℕ) (f : φ ℕ), ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ :=
  fun h => h [0, 1] ⟨ 0 ⟩

-- D i.e. seriality ◻p ⊢ ◊p : holds exactly on nonempty words.
-- On `[]` it fails, since ⟦ [] ⊨ 𝑮 f ⟧ = ⊤ₚ while ⟦ [] ⊨ 𝑭 f ⟧ = ⊥ₚ.
theorem sem_serial (w : List α) (hw : 0 < | w |) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ 𝑭 f ⟧ := by
  refine le_trans (sem_reflexivity_G w hw f) ?_
  simp only [sem]
  refine le_sup_of_le_right ?_
  have hz : ⟦ w ⊨ f ⟧ = ⟦ w ^ 0 ⊨ f ⟧ := by rw [List.drop_zero]
  rw [hz]
  have w_nonempty : 0 ∈ (Finset.range w.length) := Iff.mpr Finset.mem_range hw
  exact Finset.le_sup (f := fun j => ⟦ w^j ⊨ f ⟧) w_nonempty

-- 5 i.e euclideanity ♢p ⊢ ◻◊p : does NOT hold
-- Witness: w = ["a"] and f = ⟨"a"⟩, where ⟦ w ⊨ 𝑭 f ⟧ = ⊤ but ⟦ w ⊨ 𝑮 𝑭 f ⟧ = ⊤ₚ.
lemma not_sem_euclideanity : ¬ ∀ (w : List String) (f : φ String), ⟦ w ⊨ 𝑭 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧
  := fun h => h ["a"] ⟨ "a" ⟩

-- Corrolary from Modal properties

-- 𝑮 is monotone in its argument, position by position
lemma sem_G_mono (w : List α) (a b : φ α)
    (h : ∀ i, i < | w | → ⟦ w ^ i ⊨ a ⟧ ≤ ⟦ w ^ i ⊨ b ⟧) :
    ⟦ w ⊨ 𝑮 a ⟧ ≤ ⟦ w ⊨ 𝑮 b ⟧ := by
  simp only [sem]
  exact inf_le_inf_left ⊤ₚ (Finset.inf_mono_fun fun i hi => h i (Finset.mem_range.mp hi))

-- □p ⊢ □□p ⊢ □♢p holds because
lemma sem_G_le_G_F (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ :=
  le_trans (sem_transitivity_G w f)  -- □p ⊢ □□p
    (sem_G_mono w (𝑮 f) (𝑭 f) fun i hi => -- □p ⊢ □q if p < q
      sem_serial (w ^ i) (by simp only [List.length_drop]; lia) f) -- □□p ⊢ □♢p

-- N i.e. Necessitation Rule p ⊢ □p
theorem sem_symmetry_of_le_G (w : List α) (f : φ α) (h : ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 f ⟧) :
    ⟦ w ⊨ f ⟧ ≤ ⟦ w ⊨ 𝑮 𝑭 f ⟧ := le_trans h (sem_G_le_G_F w f)
