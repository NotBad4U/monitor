import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4
import Mealy.Logics.FLTL4.Syntax
import Mealy.Logics.FLTL4.Semantic.Denotation
import Mealy.Automata.Sequence

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
