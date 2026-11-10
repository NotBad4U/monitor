import Mathlib.Basic.ENNReal.Basic

variable (τ : Type u) [LinearOrder τ]

/--
  Range structure definition
-/
structure Range where
  mk ::
  min : τ
  max : WithTop τ
  wff_range : min ≤ max
  deriving DecidableEq, Repr

notation "𝑰" => Range

variable {τ}

def Range.contains (r:Range τ) (i:τ) : Bool :=
  (r.min ≤ i) /\ ((i : WithTop τ) ≤ r.max)

def Range.intersect (r1:Range τ) (r2:Range τ) : Bool :=
  ((r2.min ≤ r1.max) /\ (r1.min ≤ r2.max)) \/
  ((r1.min ≤ r2.max) /\ (r2.min ≤ r1.max))

def Range.merge (r1:Range τ) (r2:Range τ) : Range τ :=
  let min (i1:τ) (i2:τ) : τ := if i1 ≤ i2 then i1 else i2
  let max (i1:WithTop τ) (i2:WithTop τ) : WithTop τ := if i1 ≤ i2 then i1 else i2
  Range.mk
    (min r1.min r2.min)
    (max r1.max r2.max)
    (by
      simp [min,max]
      split_ifs with h1
      · exact r1.wff_range
      · exact le_trans (WithTop.coe_le_coe.mpr h1) r2.wff_range
      · exact le_trans (WithTop.coe_le_coe.mpr ((le_total _ _).resolve_left h1)) r1.wff_range
      · exact r2.wff_range
    )

notation r " ⊕ " r' => Range.merge r r'
