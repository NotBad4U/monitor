import Mathlib.Data.Finset.Lattice.Fold

import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4

import Mealy.Logics.FLTL4.Syntax

namespace FLTL4

variable {α} [DecidableEq α]

/--
  Notations, syntax extentions and abbrevations
-/
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
syntax :67 (name := card) "|" term "|" : term

macro_rules (kind := card)
  | `(|$w:ident|) => `(List.length $w)

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
    | `(Finset.range $n) =>
      `(⨆ $i:ident < $n, $f)
    | _ =>
      throw ()
  | `($_ $s $f) => do
    match s with
    | `(Finset.range $n) =>
      `(⨆< $n, $f)
    | _ =>
      throw ()
  | _ => throw ()

@[app_unexpander Finset.inf]
def unexpandRangeInf : Lean.PrettyPrinter.Unexpander
  | `($_ $s fun $i:ident => $f) => do
    match s with
    | `(Finset.range $n) =>
      `(⨅ $i:ident < $n, $f)
    | _ =>
      throw ()
  | `($_ $s $f) => do
    match s with
    | `(Finset.range $n) =>
      `(⨅< $n, $f)
    | _ =>
      throw ()
  | _ => throw ()

-- ``⨅ i ∈ w, f i` : meet of `f i` over the positions `i` of `w`
syntax :75 (name := drop) ident "^" term:76 : term

macro_rules (kind := drop)
  | `($w:ident^$i:term) => `(List.drop $i $w)

set_option hygiene false in
notation:200 "⟦ " w " ⊨ " p " ⟧" => sem w p

/--
  FLTL₄ semantic
-/
def sem (w : List α) : φ α → 𝔹₄
  | .true => ⊤
  | .false => ⊥
  | ~ ⟨x⟩ => x ∉ w[0]
  | ⟨x⟩ => x ∈ w[0]
  | ~ φ => (sem w φ)ᶜ
  | φ ⋁ ψ => sem w φ ⊔ sem w ψ
  | φ ⋀ ψ => sem w φ ⊓ sem w ψ
  | 𝑿 φ => if |w| > 0 then ⟦ w^1 ⊨ φ ⟧ else ⊥ₚ
  | X̅ φ => if |w| > 0 then ⟦ w^1 ⊨ φ ⟧ else ⊤ₚ
  | 𝑮 φ => ⊤ₚ ⊓ (⨅ i ∈ |w|, ⟦ w^i ⊨ φ ⟧)
  | 𝑭 φ => ⊥ₚ ⊔ (⨆ i ∈ |w|, ⟦ w^i ⊨ φ ⟧)
  | φ 𝑼 ψ => (⨆ i ∈ |w|, (⟦ w^i ⊨ ψ ⟧ ⊓ (⨅ j ∈ i, ⟦ w^j ⊨ φ ⟧))) ⊔ (⊥ₚ ⊓ (⨅ i ∈ |w|, ⟦ w^i ⊨ φ ⟧))
  | φ 𝑹 ψ => (⨅ i ∈ |w|, (⟦ w^i ⊨ ψ ⟧ ⊔ (⨆ j ∈ i, ⟦ w^j ⊨ φ ⟧))) ⊓ (⊤ₚ ⊔ (⨆ i ∈ |w|, ⟦ w^i ⊨ φ ⟧))

/--
  Semantic negation is the complement of the semantic
-/
@[simp]
lemma sem_not_eq_compl_sem (w : List α) (f : φ α) : ⟦ w ⊨ ~ f ⟧ = (⟦ w ⊨ f ⟧)ᶜ := by
  cases f with
  | ap x => simp [sem, nlookup]
  | _ => simp [sem]

/--
  Or commutativity
-/
@[simp]
lemma or_commutative : ∀ (w : List α), ∀ (a b : φ α), ⟦ w ⊨ a ⋁ b ⟧ = ⟦ w ⊨ b ⋁ a ⟧ := by
  intro w a b
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.commut_cup ..

/--
  And commutativity
-/
@[simp]
lemma and_commutativity : ∀ (w : List α), ∀ (a b : φ α), ⟦ w ⊨ a ⋀ b ⟧ = ⟦ w ⊨ b ⋀ a ⟧ := by
  intro w a b
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.commut_cap ..

/--
  Or associativity
-/
@[simp]
lemma or_associativity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋁ (b ⋁ c) ⟧ = ⟦ w ⊨ (a ⋁ b) ⋁ c ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.assoc_cup ..

/--
  And associativity
-/
@[simp]
lemma and_associativity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋀ (b ⋀ c) ⟧ = ⟦ w ⊨ (a ⋀ b) ⋀ c ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.assoc_cap ..

/--
  Or/And distributivity
-/
@[simp]
lemma or_and_distributivity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋁ (b ⋀ c) ⟧ = ⟦ w ⊨ (a ⋁ b) ⋀ (a ⋁ c) ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.distr_cup ..

/--
  And/Or distributivity
-/
@[simp]
lemma and_or_distributivity :
    ∀ (w : List α), ∀ (a b c : φ α), ⟦ w ⊨ a ⋀ (b ⋁ c) ⟧ = ⟦ w ⊨ (a ⋀ b) ⋁ (a ⋀ c) ⟧ := by
  intro w a b c
  simp [sem]
  exact BooleanLatticeProperties_𝔹₄.distr_cap ..

/--
  Semantic equivalences for construction 𝑭
-/
lemma eq_sem_F_with_U (w : List α) (f : φ α) : ⟦ w ⊨ 𝑭 f ⟧ = ⟦ w ⊨ .true 𝑼 f ⟧ := by
  simp only [sem]
  simp [sup_comm]

/--
  Semantic equivalences for construction 𝑮
-/
lemma eq_sem_G_with_R (w : List α) (f : φ α) : ⟦ w ⊨ 𝑮 f ⟧ = ⟦ w ⊨ .false 𝑹 f ⟧ := by
  simp only [sem]
  simp [inf_comm]

/-
  Semantic is the same with or without normalisation
-/
theorem norm_equiv (w : List α) (f : φ α) : ⟦ w ⊨ nrm f ⟧ = ⟦ w ⊨ f ⟧ := by
  induction f generalizing w with
  | true | false | ap _ =>
    simp [nrm]
  | not f hf =>
    simp [nrm]
    split <;> simp [sem, ← hf]  <;> simp [*, sem]       -- match/with
  | or l r hl hr | and l r hl hr =>
    simp [nrm, sem]
    split <;> simp [sem, ← hl, ← hr] <;> simp [*, sem]  -- match/with
    split <;> simp [sem, ← hl, ← hr]; simp [*]          -- if/then/else
  | next f hf | weak_next f hf =>
    simp [nrm, sem, hf]
  | «until» l r hl hr | release l r hl hr =>
    simp [nrm, sem, hl, hr]
  | globally f hf | «finally» f hf =>
    simp [nrm, sem, *]

end FLTL4
