namespace FLTL₄

inductive φ : Type (u+1) where
  | true : φ
  | false: φ
  | ap : {α : Type u} → α → φ
  | not : φ → φ
  | and : φ → φ → φ
  | or : φ → φ → φ
  | next : φ → φ
  | until : φ → φ → φ
  | weak_next : φ → φ
  | release : φ → φ → φ
  | finally : φ → φ
  | globally : φ → φ

prefix:75 "¬" => φ.not
infixr:130 "∧" => φ.and
infixr:130 "∨" => φ.or

prefix:75 "𝑿" => φ.next
prefix:75 "𝑿w" => φ.weak_next -- ??

infixr:110 "𝑼" => φ.until
infixr:110 "𝑹" => φ.release

prefix:100 "𝑭" => φ.finally
prefix:100 "𝑮" => φ.globally

notation "{: " e " :}" => φ.ap e

example : φ :=  ¬ {: 1 :} ∧ (𝑭 {: 2 :})
