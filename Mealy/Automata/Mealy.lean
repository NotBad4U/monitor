import Mathlib.Data.PFunctor.Univariate.Basic
import Mealy.TruthDomain.Core
import Mealy.TruthDomain.B4
import Mealy.Logic.Syntax

variable (α : Type u) [DecidableEq α]

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Univariate/Basic.html
--
-- paramorphism algebra, also called an R-algebra
--
--                      In
--       F (φ α)  ───────────────►  φ α
--          │                        │
--          │                        │
--  F ⟨id, fold t⟩                fold t
--          │                        │
--          ▼                        ▼
--   F (φ α × (𝔹₄ × φ α)) ──────► (𝔹₄ × φ α)
--                           t
--

-- Invariant checker
structure  mealyEff (m: Type → Type) (State: Type) (p : PFunctor)  where
  delta : (a: p.A) → State → m (State × p.B a)

def TransType {α} : φ α → Type (u + 1)
  | .true | .false | .ap _  | .next _ | .weak_next _ => 𝔹₄ × φ α
  | .not _ | .globally _ | .finally _ => (𝔹₄ × φ α) → 𝔹₄ × φ α -- (𝔹₄ × φ α) → (𝔹₄ × φ α)
  | .and _ _ | .or _ _ | .until _ _ | .release _ _ => (𝔹₄ × φ α) × (𝔹₄ × φ α) → 𝔹₄ × φ α

def fold (t: (i: φ α) → TransType i) : φ α →  𝔹₄ × φ α
  | .true => t .true
  | .false => t .false
  | .ap a => t (.ap a)
  | .next a => t (.next a)
  | .weak_next a => t (.weak_next a)
  | .not a => t (.not a) (fold t a)
  | .or a b => t (.or a b) (fold t a , fold t b)
  | .and a b => t (.and a b) (fold t a , fold t b)
  | .until a b => t (.until a b) (fold t a , fold t b)
  | .release a b => t (.release a b) (fold t a , fold t b)
  | .globally a => t (.globally a) (fold t a)
  | .finally a => t (.finally a) (fold t a)


def alg {α} [DecidableEq α] (a : α) : (state: φ α) → TransType state
  | .true => (⊤, .true)
  | .false => (⊥, .false)
  | .ap p => if p = a then (⊤, .true) else (⊥, .false)
  | .next p => (⊥ₚ, p)
  | .weak_next p => (⊤ₚ, p)
  | .not _ => fun (b, t) => (bᶜ, t)
  | .or _ _ => fun ((b1, t1),(b2 ,t2)) => (b1 ⊓ b2, .or t1 t2) -- nrm to be injected here
  | .and _ _ => fun ((b1, t1),(b2 ,t2)) => (b1 ⊔ b2, .and t1 t2) -- nrm to be injected here
  | .until _ _ => fun ((b1, t1),(b2 ,t2)) => (b1 ⊓ b2, .and t1 (.next (.until t1 t2))) -- nrm to be injected here
  | .release _ _ => fun ((b1, t1),(b2 ,t2)) => (b1 ⊔ b2, .or t1 (.weak_next (.release t1 t2))) -- nrm to be injected here
  | .finally _ => fun (b, t) => (b, .and t (.next (.finally t)))
  | .globally _ => fun (b, t) => (b, .or t (.weak_next (.globally t)))

--                     head constructor of f
--     φ α^ⁿ  ─────────────────────────────────►  φ α
--  (f₁, …, fₙ)                                    f
--       │                                         │
--       │ fold r × … × fold r                     │ fold r
--       ▼                                         ▼
--    (𝔹₄ × φ α)^ⁿ  ────────────────────────►  (𝔹₄ × φ α)
--                         r f
--              : TransType α f  =  (𝔹₄ × φ α)^ⁿ → (𝔹₄ × φ α)

variable (f: φ α)
#check TransType f

-- def transitionPF  : PFunctor where
--   A := φ α
--   B := fun state => TransType state

-- structure  mealyDep (Input: Type) (Output: Type) (p : PFunctor)  where
--   delta : (a: p.A) → Input → Output × p.B a

-- -- def fold (t: (i: φ α) → TransType i) : φ α →  𝔹₄ × φ α
-- -- def alg {α} [DecidableEq α] (a : α) : (i: φ α) → TransType i
-- def Monitor {α:Type _}  [DecidableEq α]: mealyDep α 𝔹₄ (transitionPF α) where
--   delta x s := fold (alg s) x



-- -- def fold (t: (i: φ α) → TransType i) : φ α →  𝔹₄ × φ α
-- -- def alg {α} [DecidableEq α] (a : α) : (i: φ α) → TransType i
-- def MonitorS {α:Type _}  [DecidableEq α]: mealyDepS α 𝔹₄ (transitionPF α) where
--   delta x s := fold (alg s) x

structure  mealyDep (State: Type v) (p : PFunctor)  where
  delta : (a: p.A) → State →  State × p.B a

-- 𝛿 : (i: Σ) * (s: 𝑆) → ∃ s'.
-- delta : (s : φ a) → (i: α) → δ₄ (s i)

-- Polynomial functor of the 𝔹₄ monitor: reads a letter `a : α`, emits a verdict in `𝔹₄`
def monitorPF : PFunctor where
  A := α
  B := fun _ => 𝔹₄

def δ₄ {α} [DecidableEq α] (a : α) : φ α → 𝔹₄ × φ α :=
  fold α (alg a)

-- The monitor `M₄` as a `mealyDep`: states are residual formulae
def M₄ : mealyDep (φ α) (monitorPF α) where
  delta a s := (δ₄ (α := α) a s).swap

def prop : φ String := 𝑭 ⟨"a"⟩

-- One step: read "b" from the state `prop`
#eval (M₄ String).delta "b" prop
-- (φ.and (φ.false) (φ.next (φ.finally (φ.false))), ⊥)

-- Two steps by hand: feed the new state back in
#eval
  let (s₁, v₁) := (M₄ String).delta "b" prop
  let (_, v₂) := (M₄ String).delta "a" s₁
  (v₁, v₂)
-- (⊥, ⊥ₚ)

-- A whole trace: thread the state, collect the verdicts
def run (s : φ String) : List String → List 𝔹₄
  | [] => []
  | a :: w =>
    let (s', v) := (M₄ String).delta a s
    v :: run s' w

#eval run prop ["b", "b", "a"]
-- [⊥, ⊥ₚ, ⊥]

-- Mealy machine whose interface (inputs and outputs) depends on the current state
structure mealyDepS (State : Type v) (p : State → PFunctor) where
  delta : (s : State) → (a : (p s).A) → State × (p s).B a

-- A state is decided once its residual is a constant
def decided : φ α → Bool
  | .true | .false => true
  | _ => false

-- Undecided states read letters, decided states read nothing
def statePF (s : φ α) : PFunctor where
  A := { _a : α // decided α s = false }
  B := fun _ => 𝔹₄

def M₄S : mealyDepS (φ α) (statePF α) where
  delta s a := (δ₄ a.1 s).swap

-- A decided state has no input: the monitor cannot step after a final verdict
example (a : (statePF α .true).A) : False := by
  cases a with | mk _ h => cases h

-- Runs `M₄S` over a trace, stopping as soon as the residual is decided
def runS (f : φ String) : List String → List 𝔹₄
  | [] => []
  | a :: w =>
    if h : decided String f = false then
      let (f', v) := (M₄S String).delta f ⟨a, h⟩
      v :: runS f' w
    else []

#eval runS (⟨"a"⟩ 𝑼 ⟨"b"⟩) ["a", "b", "c", "d"]
#eval runS ⟨"a"⟩ ["a", "b", "c"]







-- Mealy machine whose next state's type depends on the current state and the input
structure mealyIdx (I : Type v) (S : I → Type w) (p : I → PFunctor) where
  next : (i : I) → (p i).A → I
  delta : {i : I} → S i → (a : (p i).A) → S (next i a) × (p i).B a

section Indexed

variable {α}

-- Residual reached from `φ₀` after reading `w`
def after (φ₀ : φ α) (w : List α) : φ α :=
  w.foldl (fun f a => (δ₄ a f).2) φ₀

-- States indexed by a residual `f`: the traces from `φ₀` that lead to `f`
def Trace (φ₀ : φ α) (f : φ α) : Type u :=
  { w : List α // after φ₀ w = f }

end Indexed

def M₄I (φ₀ : φ α) : mealyIdx (φ α) (Trace φ₀) (fun _ => monitorPF α) where
  next f (a : α) := (δ₄ a f).2
  delta := fun {f} ⟨w, h⟩ (a : α) => (⟨w ++ [a], by subst h; simp [after]⟩, (δ₄ a f).1)

-- Runs `M₄I` from `φ₀`, starting with the empty trace
def runI (φ₀ : φ String) : {f : φ String} → Trace φ₀ f → List String → List 𝔹₄
  | _, _, [] => []
  | _, s, a :: w =>
    let (s', v) := (M₄I String φ₀).delta s a
    v :: runI φ₀ s' w

#eval runI (⟨"a"⟩ 𝑼 ⟨"b"⟩) ⟨[], rfl⟩ ["a", "a", "b"]


structure DMealy where
  State : Type (u + 1)
  Input : State → Type u
  Output : (s : State) → Input s → Type u
  step :
    (s : State) →
    (a : Input s) →
    Output s a × State

def instDMealy {α:Type _} : DMealy where
  State := φ α
  Input := fun _ => α
  Output := fun _ _ => 𝔹₄
  step := sorry

structure IndexedMealy where
  Q : Type
  State : Q → Type

  Input : Q → Type
  Output : (q : Q) → Input q → Q → Type

  step :
    (q : Q) →
    State q →
    (a : Input q) →
    Σ q' : Q, Output q a q' × State q'
