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

notation:130 a " ⟶ " b => (~ a) ⋁ b

/--
  Some basic examples
-/
private def exampleString : φ String := (𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩))

private def exampleNatural : φ Nat := (𝑮 (⟨1⟩ 𝑼 ⟨2⟩)) ⋀ (𝑮 (~ ⟨3⟩))

-- Normalisation

def simplify  : φ α → φ α
  | .true => .true
  | .false => .false
  | .ap a => .ap a
  | .not f =>
      match simplify f with
      | .true => .false
      | .false => .true
      | f => .not f
  | .and l r =>
      match simplify l, simplify r with
      | .true, r => r
      | l, .true => l
      | .false, _ => .false
      | _, .false => .false
      | l, r => if l = r then l else .and l r
  | .or l r =>
      match simplify l, simplify r with
      | .false, r => r
      | l, .false => l
      | .true, _ => .true
      | _, .true => .true
      | l, r => if l = r then l else .or l r
  | .next e => .next (simplify e)
  | .weak_next e => .weak_next (simplify e)
  | .until l r => .until (simplify l) (simplify r)
  | .release l r => .release (simplify l) (simplify r)
  | .finally e => .finally (simplify e)
  | .globally e => .globally (simplify e)

#eval simplify (⟨2⟩ ⋀ (.true ⋀ ⟨2⟩))

theorem simplify_simplify_eq_simplify : ∀ e: φ α,simplify (simplify e) = simplify e := by
  intro e; induction e <;> grind [simplify]

-- def norms : φ α → φ α := fun e =>
--     let e' := norm e
--     if e' = e
--     then e
--     else norms e'
