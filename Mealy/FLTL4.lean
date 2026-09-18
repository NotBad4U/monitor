import Mealy.TruthDomain
import Mathlib.Data.Finset.Lattice.Fold
import LeanSearchClient

open TruthDomain.TruthDomain_𝔹₄

namespace FLTL₄

variable (α : Type u) [DecidableEq α]

inductive  φ : Type (u + 1) where
  | true : φ
  | false: φ
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

prefix:60 "~ " => φ.not
infixr:130 " ⋀ " => φ.and
infixr:130 " ⋁ " => φ.or

prefix:75 "𝑿 " => φ.next
prefix:75 "X̅ " => φ.weak_next -- Je n'arrive pas à combiner \MIX et \overline ou \bar

infixr:110 " 𝑼 " => φ.until
infixr:110 " 𝑹 " => φ.release

prefix:100 "𝑭 " => φ.finally
prefix:100 "𝑮 " => φ.globally

notation "⟪ " e " ⟫" => φ.ap e

notation " ⊤ " => φ.true
notation " ⊥ " => φ.false

def exampleNat : φ ℕ := (𝑮 (⟪ 1 ⟫ 𝑼 ⟪ 2 ⟫)) ⋀ (𝑮 (~ ⟪ 0 ⟫))

def exampleString : φ String := (𝑮 (⟪ "a" ⟫ 𝑼 ⟪ "b" ⟫)) ⋀ (𝑮 (~ ⟪ "c" ⟫))

set_option hygiene false in
notation:200 "⟦ " w " ⊨ " p " ⟧" => sem w p

abbrev lookup (w : List α) (i : ℕ) (x : α) : 𝔹₄ := if w[i - 1]? = .some x then .top else .bot
abbrev nlookup (w : List α) (i : ℕ) (x : α) : 𝔹₄ := if w[i - 1]? = .some x then .bot else .top

syntax:50 (name := memAt) term:51 " ∈ " ident "[" term "]" : term
syntax:50 (name := notMemAt) term:51 " ∉ " ident "[" term "]" : term

macro_rules (kind := memAt)
  | `($x ∈ $w:ident[$i]) => `(lookup _ $w $i $x)

macro_rules (kind := notMemAt)
  | `($x ∉ $w:ident[$i]) => `(nlookup _ $w $i $x)


macro_rules (kind := notMemAt)
  | `($x ∉ $w:ident[$i]) => `(nlookup _ $w $i $x)

-- `| w |` : join / meet of `f i` over the positions `i` of `w`
syntax:67 (name := card) "| " term " |" : term
-- `⨆ i ∈ w, f i` : join of `f i` over the positions `i` of `w`
syntax:67 (name := supPos) "⨆ " ident " ∈ " ident ", " term : term
-- ``⨅ i ∈ w, f i` : meet of `f i` over the positions `i` of `w`
syntax:67 (name := infPos) "⨅ " ident " ∈ " ident ", " term : term

macro_rules (kind := card)
  | `(| $w:ident |) => `(List.length $w)

macro_rules (kind := supPos)
  | `(⨆ $i:ident ∈ $w:ident, $f) => `((Finset.range $w).sup fun $i => $f)

macro_rules (kind := infPos)
  | `(⨅ $i:ident ∈ $w:ident, $f) => `((Finset.range $w).inf fun $i => $f)

def sem (w : List α) : φ α → 𝔹₄
  | ⊤ => .top
  | ⊥ => .bot
  | ~ ⟪ x ⟫ => x ∉ w[0]
  | ⟪ x ⟫ => x ∈ w[0]
  | ~ φ => (⟦ w ⊨ φ ⟧) ᶜ
  | φ ⋁ ψ => ⟦ w ⊨ φ ⟧ ⊔ ⟦ w ⊨ ψ ⟧
  | φ ⋀ ψ => ⟦ w ⊨ φ ⟧ ⊓ ⟦ w ⊨ ψ ⟧
  | 𝑿 φ => if w.isEmpty = false then ⟦ w.tail ⊨ φ ⟧ else .botₚ
  | X̅ φ => if w.isEmpty = false then ⟦ w.tail ⊨ φ ⟧ else .topₚ
  | 𝑮 φ => .botₚ ⊔ (⨆ i ∈ w.length, ⟦ w.drop i ⊨ φ ⟧)
  | 𝑭 φ => .topₚ ⊓ (⨅ i ∈ w.length, ⟦ w.drop i ⊨ φ ⟧)
  | φ 𝑼 ψ => ⨆ i ∈ w.length, (⟦ w.drop i ⊨ ψ ⟧ ⊓ (⨅ j ∈ i, ⟦ w.drop j ⊨ φ ⟧)) ⊔ (.botₚ ⊓ (⨆ i ∈ w.length, ⟦ w.drop i ⊨ φ ⟧))
  | φ 𝑹 ψ => ⨆ i ∈ w.length, (⟦ w.drop i ⊨ ψ ⟧ ⊓ (⨅ j ∈ i, ⟦ w.drop j ⊨ φ ⟧)) ⊔ (.topₚ ⊓ (⨆ i ∈ w.length, ⟦ w.drop i ⊨ φ ⟧))
