/-
  Mealy machines as coalgebras.

  Follows C.B. Aberlé, "Compositional Program Verification with Polynomial Functors in
  Dependent Type Theory" (arXiv:2604.01303). Lean has no coinductive records, so the
  coinductive `Mealy` and `DepMealy` of the paper are presented with an explicit state.
-/
import Mathlib.Data.PFunctor.Univariate.Basic
import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4
import Mealy.Logics.FLTL4.Syntax
import Mealy.Automata.Mealy

variable {α : Type u} [DecidableEq α]

/-
  Polynomial functors

      P(X) = Σ (a : A), X^(B(a))

  To follow more the litterature, Mathlib's `PFunctor` is named `Poly` here.
-/
abbrev Poly.{a, b} := PFunctor.{a, b}

/-
  Dependent polynomial over Poly p = (A, B) (§ 5.1):

      DepPoly (A , B) = Σ (C : A → Set), (a : A) → C(a) → B(a) → Set

  where:
  * Pre(a) is the precondition on the input a;
  * Post(a, c, b) is the postcondition on the output b, given evidence c that Pre(a) holds.
-/
structure DepPoly (p : Poly) where
  Pre  : p.A → Type
  Post : (a : p.A) → Pre a → p.B a → Type

/-
  Mealy machine with interface p = (A, B) (Definition 4.1 of the paper):

      app : ∏ (s : S), ∏ (a : A), B(a) × S

  where:
  * S is the type of states, and state is the current one;
  * A is the type of inputs;
  * B(a) is the output type, depending on the input a.
-/
structure Mealy (p : Poly) where
  S     : Type a
  state : S
  app   : S → (a : p.A) → p.B a × S

def Mealy.ofδ (f : φ α) : Mealy ⟨α, fun _ => 𝔹₄⟩ where
  S := φ α
  state := f
  app s (a : α) := δ a s

-- Read an input `a` and output `o: p.B a` and the machine in its next state.
def Mealy.step {p : Poly} (m : Mealy p) (a : p.A) : p.B a × Mealy p :=
  ((m.app m.state a).1, { m with state := (m.app m.state a).2 })

def runMealyPoly {p : Poly} (m : Mealy p) : m.S → List p.A → List ((a : p.A) × p.B a)
  | _, [] => []
  | s, a :: w => ⟨a, (m.app s a).1⟩ :: runMealyPoly m (m.app s a).2 w

/-
  Bisimulation between Mealy machines `m1` and `m2` with the same interface `p`:

                a / o
          s₁ ───────────► s₁'          (o, s₁') = m1.app s₁ a
          │               │
        R │               │ R
          │               │
          s₂ ───────────► s₂'          (o, s₂') = m2.app s₂ a
                a / o
-/
structure Mealy.Bisim {p : Poly} (m1 m2 : Mealy p) where
  R : m1.S → m2.S → Prop
  state_ok : R m1.state m2.state
  app_ok : ∀ s₁ s₂, R s₁ s₂ → ∀ a,
            (m1.app s₁ a).1 = (m2.app s₂ a).1 ∧ R (m1.app s₁ a).2 (m2.app s₂ a).2

-- `m1 ≈ m2` is a bisimulation between `m1` and `m2`.
instance MealyEquiv {p : Poly} : HasEquiv (Mealy p) := ⟨Mealy.Bisim⟩


private def m0 := Mealy.ofδ ((𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩)))
private def m2 := ((m0.step "a").2.step "a").2
#eval (m0.step "a").1  -- ⊥ₚ
#eval (m2.step "b").1  -- ⊤ₚ

/-
  Dependent Mealy machine for the specification (p, r) over the Mealy machine m (§ 6.1):

      appD : ∏ (a : A), ∏ (c : Pre(a)), Post(a, c, o) × DepMealy p r m'
             where (o, m') = app(a)

  An invariant `Inv` on the states of `m`:
  it holds in the current state, and from a state satisfying it, any input satisfying `Pre`
  produces an output satisfying `Post` and leads to a state satisfying `Inv` again.
-/
structure DepMealy (p : Poly) (r : DepPoly p) (m : Mealy p) where
  Inv      : m.S → Prop
  state_ok : Inv m.state
  appD     : (s : m.S) → Inv s → (a : p.A) → (c : r.Pre a) →
               r.Post a c (m.app s a).1 ×' Inv (m.app s a).2

/-- One step of a verified machine: the postcondition, and the verified machine in its next state. -/
def DepMealy.step {p : Poly} {r : DepPoly p} {m : Mealy p}
    (d : DepMealy p r m) (a : p.A) (c : r.Pre a) :
    r.Post a c (m.step a).1 ×' DepMealy p r (m.step a).2 :=
  let h := d.appD m.state d.state_ok a c
  ⟨h.1,
   { Inv      := d.Inv
     state_ok := h.2
     appD     := d.appD }⟩
