-- A library of operators over relations, to define transition sequences and their properties.

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Check

variable {A: Type} -- the type of states
variable {R: A → A → Prop} -- the transition relation between states

-- Zero, one or several transitions: reflexive transitive closure of R.
inductive star : A → A → Prop where
  | refl (a: A): star a a
  | step (a b c: A) :  R a b → star b c → star a c

local infix:50 " ⟶* " => star (R := R)

lemma star_one : forall (a b: A), R a b → a ⟶* b := by
  intro a b h
  exact star.step a b b h (star.refl b)

lemma star_trans (a b : A): a ⟶* b → forall c, b ⟶* c → a ⟶* c := by
  intro h1 c h2
  induction h1 with
  | refl => exact h2
  |  step x y z hr _ ih =>
    exact star.step x y c hr (ih h2)

-- One or several transitions: transitive closure of R.

inductive plus : A → A → Prop where
  | plus_left: forall a b c,
      R a b → b ⟶* c → plus a c

local infix:50 " ⟶⁺ " => plus (R := R)

lemma plus_one : forall a b, R a b → a ⟶⁺ b := by
  intro a b h
  exact plus.plus_left a b b h (star.refl  b)

lemma plus_star : forall a b, a ⟶⁺ b → a ⟶* b := by
  intro a b h
  match h with
  | plus.plus_left _ x _ hr hs => exact star.step a x b hr hs

lemma plus_star_trans_l : forall a b c, a ⟶⁺ b → b ⟶* c → a ⟶* c := by
  intro a b c h1 h2
  exact star_trans a b (plus_star a b h1) c h2

lemma plus_star_trans_r : forall a b c,  a ⟶* b → b ⟶⁺ c  → a ⟶* c := by
  intro a b c h1 h2
  exact star_trans a b h1 c (plus_star b c h2)

-- Absence of transitions from a state.

def irred (a: A) : Prop := forall b, ¬ R a b

def all_seq_inf (a : A ) : Prop := forall b, a ⟶* b → exists c, R b c

def infseq (a: A) : Prop :=
  exists P: A → Prop, P a ∧ (forall a1, P a1 → exists a2, R a1 a2 ∧ P a2)



-- A coinduction principle considers a set X where for every a in X,
-- we can make one or several transitions to reach a state b that belongs to X.

lemma infseq_coinduction_principle:
    forall (P: A → Prop),
    (forall a, P a → exists b, a ⟶⁺ b ∧ P b) →
    forall a, P a → infseq (R := R) a := by
  intro P hP a hPa
  refine ⟨fun x => exists y, x ⟶* y ∧ P y, ⟨a, star.refl a, hPa⟩, ?_⟩
  intro a1 ⟨a2, h12, hP2⟩
  cases h12 with
  | refl =>
    obtain ⟨a3, h13, hP3⟩ := hP a1 hP2
    match h13 with
    | plus.plus_left _ b _ hr hs => exact ⟨b, hr, a3, hs, hP3⟩
  | step _ b _ hr hs =>
    exact ⟨b, hr, a2, hs, hP2⟩
