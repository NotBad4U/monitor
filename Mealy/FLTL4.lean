import Mealy.TruthDomain

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

prefix:75 "¬ " => φ.not
infixr:130 " ∧ " => φ.and
infixr:130 " ∨ " => φ.or

prefix:75 "𝑿 " => φ.next
prefix:75 "X̅ " => φ.weak_next -- Je n'arrive pas à combiner \MIX et \overline ou \bar

infixr:110 " 𝑼 " => φ.until
infixr:110 " 𝑹 " => φ.release

prefix:100 "𝑭 " => φ.finally
prefix:100 "𝑮 " => φ.globally

notation "{ " e " }" => φ.ap e

example : φ :=  ¬ { 1 } ∧ (𝑭 { 2 })

set_option hygiene false in
notation:200 "⟦ " w " ⊨ " p " ⟧" => sem w p

open TruthDomain.TruthDomain_𝔹₄ in
def sem { W : Type } (w : W) : φ → 𝔹₄
  | .true    => .top
  | .false   => .bot
  | .not φ   => compl (⟦ w ⊨ φ ⟧)
  | .or φ ψ  => ⟦ w ⊨ φ ⟧ ⊔ ⟦ w ⊨ ψ ⟧
  | .and φ ψ => ⟦ w ⊨ φ ⟧ ⊓ ⟦ w ⊨ ψ ⟧
  | _        => .bot
