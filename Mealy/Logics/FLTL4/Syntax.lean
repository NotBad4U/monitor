-- uncomment for dev mode only
set_option pp.parens true
variable (α : Type u) [DecidableEq α]

/--
  FLTL algebraic data type
-/
inductive φ : Type u where
  | true : φ
  | false : φ
  | ap : α → φ
  | not : φ → φ
  | and : φ → φ → φ
  | or : φ → φ → φ
  | next : φ → φ
  | weak_next : φ → φ
  | until : φ → φ → φ
  | release : φ → φ → φ
  | finally : φ → φ
  | globally : φ → φ
  deriving DecidableEq, Repr

variable {α}

/--
  Syntax annotations
-/
prefix:60 "~ " => φ.not

infixr:130 " ⋀ " => φ.and

infixr:130 " ⋁ " => φ.or

prefix:75 "𝑿 " => φ.next

prefix:75 "X̅ " => φ.weak_next

infixr:110 " 𝑼 " => φ.until

infixr:110 " 𝑹 " => φ.release

prefix:100 "𝑭 " => φ.finally

prefix:100 "𝑮 " => φ.globally

notation "⟨ " e " ⟩" => φ.ap e

notation:130 (name := φ.impl) a " ⟶ " b => (~ a) ⋁ b

/--
  Some basic examples
-/
private def exampleString : φ String := (𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩))

private def exampleNatural : φ Nat := (𝑮 (⟨1⟩ 𝑼 ⟨2⟩)) ⋀ (𝑮 (~ ⟨3⟩))

-- Normalisation

def FLTL4.nrm : φ α → φ α
  | .true => .true
  | .false => .false
  | .ap a => .ap a
  | .not f =>
      match nrm f with
      | .true => .false
      | .false => .true
      | f => .not f
  | .and l r =>
      match nrm l, nrm r with
      | .true, r => r
      | .false, _ => .false
      | l, .true => l
      | _, .false => .false
      | l, r => if l = r then l else .and l r
  | .or l r =>
      match nrm l, nrm r with
      | .false, r => r
      | .true, _ => .true
      | l, .false => l
      | _, .true => .true
      | l, r => if l = r then l else .or l r
  | .next e => .next (nrm e)
  | .weak_next e => .weak_next (nrm e)
  | .until l r => .until (nrm l) (nrm r)
  | .release l r => .release (nrm l) (nrm r)
  | .finally e => .finally (nrm e)
  | .globally e => .globally (nrm e)

-- #eval nrm (⟨2⟩ ⋀ (.true ⋀ ⟨2⟩))

theorem nrm_nrm_eq_nrm : ∀ e: φ α,FLTL4.nrm (FLTL4.nrm e) = FLTL4.nrm e := by
  intro e; induction e <;> grind [FLTL4.nrm]
