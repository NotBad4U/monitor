-- uncomment for dev mode only
set_option pp.parens true
variable (α : Type u) [DecidableEq α]

/--
  FLTL algebraic data type
-/
inductive φ : Type (u + 1) where
  | true : φ
  | false : φ
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
def exampleString : φ String :=
  (𝑮 (⟨"a"⟩ 𝑼 ⟨"b"⟩)) ⋀ (𝑮 (~ ⟨"c"⟩))

def exampleNatural : φ Nat :=
  (𝑮 (⟨1⟩ 𝑼 ⟨2⟩)) ⋀ (𝑮 (~ ⟨3⟩))
