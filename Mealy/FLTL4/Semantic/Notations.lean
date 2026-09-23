import Mathlib.Data.Finset.Lattice.Fold

import Mealy.TruthDomain.B4

import Mealy.FLTL4.Definition

variable {α} [DecidableEq α]

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

set_option hygiene false in
notation:200 "⟦ " w " ⊨ " p " ⟧" => sem w p
