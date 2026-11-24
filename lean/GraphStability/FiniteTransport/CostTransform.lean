import Mathlib.Analysis.Normed.Ring.Basic

/-!
# From two transport potentials to one
-/

noncomputable section

namespace GraphStability.FiniteTransport

variable {V : Type*} [Fintype V]

/-- The cost transform of the second potential is the infimum of `c x y - β y` over `y`.
On a finite vertex set the infimum is the minimum in equation (S79). -/
def costTransform (c : V → V → ℝ) (β : V → ℝ) (x : V) : ℝ :=
  ⨅ y, c x y - β y

/-- A cost transform is bounded above by each term defining it. -/
theorem costTransform_le (c : V → V → ℝ) (β : V → ℝ) (x y : V) :
    costTransform c β x ≤ c x y - β y :=
  Finite.ciInf_le _ y

/-- Under the triangle inequality, `g x - g y ≤ c x y` for the cost transform `g`. -/
theorem costTransform_sub_le (c : V → V → ℝ)
    (htriangle : ∀ x y z, c x z ≤ c x y + c y z)
    (β : V → ℝ) (x y : V) :
    costTransform c β x - costTransform c β y ≤ c x y := by
  rw [sub_le_comm]
  haveI : Nonempty V := ⟨y⟩
  apply le_ciInf
  intro z
  linarith [costTransform_le c β x z, htriangle x y z]

omit [Fintype V] in
/-- A feasible first potential lies below the transform of the second. -/
theorem le_costTransform (c : V → V → ℝ) (α β : V → ℝ)
    (hfeasible : ∀ x y, α x + β y ≤ c x y) (x : V) :
    α x ≤ costTransform c β x := by
  haveI : Nonempty V := ⟨x⟩
  exact le_ciInf fun y => le_sub_iff_add_le.mpr (hfeasible x y)

/-- If `c x x = 0` and `α x + β y ≤ c x y`, replacing `(α, β)` by the cost
transform and its negative does not decrease the dual objective for
non-negative marginals. -/
theorem pairing_le_costTransform (c : V → V → ℝ)
    (hself : ∀ x, c x x = 0) (α β μ ν : V → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hfeasible : ∀ x y, α x + β y ≤ c x y) :
    (∑ x, μ x * α x) + (∑ x, ν x * β x) ≤
      (∑ x, μ x * costTransform c β x) - ∑ x, ν x * costTransform c β x := by
  have hfirst : (∑ x, μ x * α x) ≤ ∑ x, μ x * costTransform c β x :=
    Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (le_costTransform c α β hfeasible x) (hμ x)
  have hsecond : (∑ x, ν x * β x) ≤ ∑ x, ν x * (-costTransform c β x) :=
    Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (by linarith [costTransform_le c β x x, hself x]) (hν x)
  simpa only [mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg] using
    add_le_add hfirst hsecond

end GraphStability.FiniteTransport
