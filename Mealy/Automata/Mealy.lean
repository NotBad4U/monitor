import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4
import Mealy.Logics.FLTL4.Syntax
import Mealy.Logics.FLTL4.Semantic.Denotation
import Mealy.Automata.Sequence
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Profunctor.Basic

variable {α : Type u} [DecidableEq α]

/--
  Verdict of a formula on the empty trace, i.e. `⟦ [] ⊨ f ⟧`
-/
def ε : φ α → 𝔹₄
  | .true => ⊤
  | .false => ⊥
  | ⟨_⟩ => ⊥
  | ~ f => (ε f)ᶜ
  | f ⋁ g => ε f ⊔ ε g
  | f ⋀ g => ε f ⊓ ε g
  | 𝑿 _ => ⊥ₚ
  | X̅ _ => ⊤ₚ
  | _ 𝑼 _ => ⊥ₚ
  | _ 𝑹 _ => ⊤ₚ
  | 𝑭 _ => ⊥ₚ
  | 𝑮 _ => ⊤ₚ

--
lemma sem_nil (f : φ α) : sem [] f = ε f := by
  induction f with
  | not f ih => rw [sem_not_eq_compl_sem, ih]; rfl
  | ap => simp [sem, ε, lookup]
  | _ => simp_all [sem, ε]


/--
  Transition: reading event `a` in state `f` outputs the verdict on the trace
  ending at `a`, and moves to the residual formula to check on the rest of the trace.
-/
def δ : α → φ α → 𝔹₄ × φ α
  | _, .true  => (⊤, .true)
  | _, .false => (⊥, .false)
  | a, ⟨p⟩  => if a = p then (⊤, .true) else (⊥, .false)
  | a, ~ ⟨p⟩ => if a = p then (⊥, .false) else (⊤, .true)
  | a, ~ f =>
    let (v, f') := δ a f
    (vᶜ, ~ f')
  | a, f ⋁ g =>
    let (vf, f') := δ a f
    let (vg, g') := δ a g
    (vf ⊔ vg, f' ⋁ g')
  | a, f ⋀ g =>
    let (vf, f') := δ a f
    let (vg, g') := δ a g
    (vf ⊓ vg, f' ⋀ g')
  | _, 𝑿 f  => (ε f, f)
  | _, X̅ f => (ε f, f)
  -- f U g  ≡  g ∨ (f ∧ X (f U g))
  | a, f 𝑼 g =>
    let (vf, f') := δ a f
    let (vg, g') := δ a g
    (vg ⊔ (vf ⊓ ⊥ₚ),
     g' ⋁ (f' ⋀ (f 𝑼 g)))
  -- f R g  ≡  g ∧ (f ∨ X̅ (f R g))
  | a, f 𝑹 g =>
    let (vf, f') := δ a f
    let (vg, g') := δ a g
    (vg ⊓ (vf ⊔ ⊤ₚ),
     g' ⋀ (f' ⋁ (f 𝑹 g)))
  -- F f  ≡  f ∨ X F f
  | a, 𝑭 f =>
    let (vf, f') := δ a f
    (vf ⊔ ⊥ₚ, f' ⋁ (𝑭 f))
  -- G f  ≡  f ∧ X̅ G f
  | a, 𝑮 f =>
    let (vf, f') := δ a f
    (vf ⊓ ⊤ₚ, f' ⋀ (𝑮 f))

/--
  Run the Mealy machine on a finite trace: starting from formula `f`, feed the
  events one by one to `δ`, emitting after each event the verdict together with
  the residual formula the machine continues from.
-/
def run : φ α → List α → List (𝔹₄ × φ α)
  | _, [] => []
  | f, a :: w =>
    let (v, f') := δ a f
    (v, f') :: run f' w

/--
  Verdict of the last step of `run`, i.e. the verdict on the whole trace.
  On the empty trace no event is read, so the verdict is `ε f`.
  QUESTION: should we combine use un in combine ? Proof will be affected.
-/
def final : φ α → List α → 𝔹₄
  | f, [] => ε f
  | f, [a] => (δ a f).1
  | f, a :: b :: w => final (δ a f).2 (b :: w)

-- 𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩) ⋀ 𝑮 (~ ⟨"c"⟩)
private def ex := ((𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩)))

#eval run ex ["a", "a", "b", "b"]
#eval final ex ["a", "a", "b", "b"] -- ⊤ₚ

/-
  Correctness of the Mealy's machine transition function w.r.t. the denotational semantics
-/
theorem eq_verdict_δ_sem : ∀ (w : List α) (f : φ α), sem w f = final f w := by
  sorry

/-
  type: ∏ (s : S), ∏ (i : I(s)), Σ (o : O(s, i)), S

  where:
  * S is the type of states;
  * I is the type of valid inputs;
  * and O is the output type.
-/
structure MealyNoDep (I : Type u) (O : Type v) where
  S : Type u
  init  : S
  app  : S → I → O × S -- ≃ S × I → O × S that you can find in the litterature

/--
  Mealy machine monitoring FLTL4 formula (`f`: φ α) denoting φ α × α → 𝔹₄ × φ α
-/
def MealyNoDep.from (f : φ α) : MealyNoDep α 𝔹₄ where
  S := φ α
  init := f
  app s a := δ a s

private def ex_meal := MealyNoDep.from ex

#eval (ex_meal.app (MealyNoDep.from ex).init "c").1 -- ⊥

/-
  Bisimulation between Mealy machines `m₁` and `m₂` with the same inputs and outputs:

                i / o
          s₁ ───────────► s₁'          (o, s₁') = m₁.app s₁ i
          │               │
        R │               │ R
          │               │
          s₂ ───────────► s₂'          (o, s₂') = m₂.app s₂ i
                i / o
-/
structure MealyNoDep.Bisim {I : Type} {O : Type} (m₁ m₂ : MealyNoDep I O) where
  R       : m₁.S → m₂.S → Prop
  init_ok : R m₁.init m₂.init
  app_ok  : ∀ s₁ s₂, R s₁ s₂ → ∀ i,
              (m₁.app s₁ i).1 = (m₂.app s₂ i).1 ∧ R (m₁.app s₁ i).2 (m₂.app s₂ i).2

-- `m₁ ≈ m₂` is a bisimulation between `m₁` and `m₂`.
instance MealyNoDepEquiv {I : Type} {O : Type} : HasEquiv (MealyNoDep I O) := ⟨MealyNoDep.Bisim⟩

/-
  type: ∏ (s : S), ∏ (i : I(s)), Σ (o : O(s, i)), S

  where:
  * S is the type of states;
  * I(s) is the type of valid inputs in state s;
  * O(s, i) is the output type, depending on the current state and input.
-/
structure MealyDep where
  S    : Type u
  I    : S → Type v
  O    : (s : S) → I s → Type w
  init : S
  app : (s : S) → (i : I s) → (O s i × S)

-- NOTE: I do not know if it usefull
def MealyDep.from (f : φ α) : MealyDep where
  S := φ α
  I := (fun _ => α)
  O := (fun _ _ => 𝔹₄)
  init := f
  app s a := δ a s

private def ex_mealD := MealyDep.from ex

#eval (ex_mealD.app ex_mealD.init "c").1 -- ⊥


def MealyNoDep.toDep {I : Type} {O : Type} (m : MealyNoDep I O) : MealyDep where
  S := m.S
  I := (fun _ => I)
  O := (fun _ _ => O)
  init := m.init
  app := m.app

/-
  Idea come from §6 of "Compositional Program Verification with Polynomial Functors in Dependent Type Theory"

  type: Σ (Inv : S → Prop), Inv(init) ∧ Π s, Inv(s) → Π i, Pre(i) → Post(i, o) ∧ Inv(s')

  A machine `m` together with an inductive invariant `Inv` on its states:
  * Pre(i) is the precondtion on the inputs;
  * Post(i, o) is postcondition on the output produced when reading input i;
  * Inv(s) is a state invariant.d
-/
structure MealyInv
    {I : Type u} {O : Type v}
    (m : MealyNoDep I O)
    (Pre : I → Prop)
    (Post : I → O → Prop) where
  Inv : m.S → Prop
  init_ok : Inv m.init
  app_ok :
    ∀ (s : m.S), Inv s →
    ∀ (i : I), Pre i →
      Post i (m.app s i).1 ∧
      Inv (m.app s i).2

namespace MealyCategory

/-
         i / o
   s ───────────► s'
   │              │
 map              map
   │              │
   ▼              ▼
 map s ─────────► map s'
         i / o
-/
structure MealyNoDep.Hom {I : Type} {O : Type} (X Y : MealyNoDep I O) where
  map: X.S → Y.S
  map_init: map X.init = Y.init
  map_out : ∀ s i, (Y.app (map s) i).1 = (X.app s i).1
  map_next : ∀ s i, (Y.app (map s) i).2 = map (X.app s i).2

def MealyNoDep.Id  {I : Type} {O : Type} (X : MealyNoDep I O) : MealyNoDep.Hom X X  where
  map := id
  map_init := by rfl
  map_out := by grind
  map_next := by grind

instance MealyNoDepCat (I : Type) (O : Type) : CategoryTheory.Category (MealyNoDep I O) where
  Hom X Y := MealyNoDep.Hom X Y
  id X := MealyNoDep.Id X
  comp f g :=
    { map := g.map ∘ f.map
      map_init := by simp [f.map_init, g.map_init]
      map_out := fun s i => by simp [f.map_out, g.map_out]
      map_next := fun s i => by simp [f.map_next, g.map_next] }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-
  A heteromorphism between two Mealy machines `X : Mealy I1 O1` and `Y : Mealy I2 O2`
  is a state map `map : Y.S → X.S` together with a pre-composition and a post-composition:
  * `lmap : I1 → I2` translates every input of `X` into an input of `Y`;
  * `rmap : O2 → O1` translates every output of `Y` into an output of `X`.

        ┌───────────────────── X : Mealy I1 O1 ────────────────────────────┐
        │                                                                  │
        │  ┌──────┐         ┌────────────────────────┐         ┌──────┐    │
  ──────┼─►│ lmap ├────────►│  Y : Mealy I2 O2       ├────────►│ rmap ├────┼──────►
   I1   │  └──────┘   I2    └────────────────────────┘    O2   └──────┘    │   O1
        │                                                                  │
        │                                                                  │
        └──────────────────────────────────────────────────────────────────┘

  and should respect the universal properties that the outputs agree:
  `(X.app s i).1 = rmap (Y.app (map s) (lmap i)).1`
  and the next states agree:
  `map (X.app s i).2 =  (Y.app (map s) (lmap i)).2`

  The following commutative diagram illustrates the universal properties:

                map × lmap
  X.S × I1 ───────────────► Y.S × I2
      │                         │
    X.app                     Y.app
      │                         │
      ▼                         ▼
  O1 × X.S ◄─────────────── O2 × Y.S
                rmap × map


-/

-- For a profunctor `H : Cᵒᵖ × D ⥤ Type`, `d ∈ D` and `c ∈ C`, the set `Hom(d, c)`
-- is also called the set of heteromorphisms from `d` to `c`.
-- source: https://ncatlab.org/nlab/show/profunctor
structure MealyNoDep.Het {I1 I2 : Type} {O1 O2 : Type}
    (lmap : I1 → I2) (rmap : O2 → O1) (X : MealyNoDep I1 O1) (Y : MealyNoDep I2 O2)  where
  map : X.S → Y.S
  map_init : map X.init = Y.init
  output_agree: forall s i, (X.app s i).1 = rmap (Y.app (map s) (lmap i)).1
  next_state_agree: forall s i, map (X.app s i).2 =  (Y.app (map s) (lmap i)).2

/--
  The profunctor `MealyNoDep I2 O2 ⥤ (MealyNoDep I1 O1)ᵒᵖ ⥤ Type` of heteromorphisms
  over the fixed wiring `(f, g)`.

  * Object are `Het f g X Y`: `Y`
  * `map ψ φ` transports a heteromorphism along machine morphisms with `φ : X ⟶ X'` and `ψ : Y ⟶ Y'`:

      ┌──── X' ────┐                    ┌──── X ────┐
      │  ┌── Y ──┐ │     map ψ φ        │  ┌─ Y' ─┐ │
      │  └───────┘ │  ──────────────►   │  └──────┘ │
      └────────────┘                    └───────────┘
       h : Het X' Y                      Het X Y'

    on states:  X.S ──φ.map──► X'.S ──h.map──► Y.S ──ψ.map──► Y'.S
-/
def MealyNoDepProfunctor {I1 I2 : Type} {O1 O2 : Type} (f : I1 → I2) (g : O2 → O1) :
  CategoryTheory.Profunctor (MealyNoDep I2 O2) (MealyNoDep I1 O1) :=
  CategoryTheory.Profunctor.ofCore
    { obj Y X := MealyNoDep.Het f g X Y
      map ψ φ := TypeCat.ofHom fun h =>
        { map := ψ.map ∘ h.map ∘ φ.map -- composition of state maps such that Y.S →^* X'.S
          map_init := by simp [φ.map_init, h.map_init, ψ.map_init]
          output_agree := by
            intros
            simp only [Function.comp]
            rw [ψ.map_out, ← h.output_agree, φ.map_out]
          next_state_agree := by
            intros
            simp only [Function.comp]
            rw [ψ.map_next, ← h.next_state_agree, φ.map_next]
        }
      map_id := fun X Y => rfl
      map_comp := fun X Y A B => rfl
    }
