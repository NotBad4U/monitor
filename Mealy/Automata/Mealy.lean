import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4
import Mealy.Logic.Syntax
import Mealy.Logic.Semantic.Denotation

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
private def fltl4prop := ((𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩)))

#eval run fltl4prop ["a", "a", "b", "b"]
#eval final fltl4prop ["a", "a", "b", "b"] -- ⊤ₚ

/-
  Correctness of the Mealy's machine transition function w.r.t. the denotational semantics
-/
theorem eq_verdict_δ_sem : ∀ (w : List α) (f : φ α), sem w f = final f w := by
  sorry
