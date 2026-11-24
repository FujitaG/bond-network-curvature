import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Effective curvature (equation (S35))
-/

noncomputable section

namespace GraphStability

/-- The effective curvature of a limiting variance `V ≥ 2`: the fraction lost
per round by the equivalent bond with the same limiting variance. -/
def effectiveCurvature (V : ℝ) : ℝ := 1 - Real.sqrt (1 - 2 / V)

/-- The effective curvature of a limiting variance `V ≥ 2` is positive. -/
theorem effectiveCurvature_pos {V : ℝ} (hV : 2 ≤ V) : 0 < effectiveCurvature V := by
  rw [effectiveCurvature, sub_pos, Real.sqrt_lt' zero_lt_one, one_pow, sub_lt_self_iff]
  exact div_pos zero_lt_two (zero_lt_two.trans_le hV)

/-- The effective curvature is at most `1`. -/
theorem effectiveCurvature_le_one (V : ℝ) : effectiveCurvature V ≤ 1 :=
  sub_le_self 1 (Real.sqrt_nonneg _)

/-- The effective curvature is non-increasing in the limiting variance on
`[2, ∞)`. -/
theorem effectiveCurvature_antitoneOn : AntitoneOn effectiveCurvature (Set.Ici 2) := by
  intro V₁ (h1 : 2 ≤ V₁) V₂ _ h12
  have hV1pos : 0 < V₁ := by linarith
  unfold effectiveCurvature
  exact sub_le_sub_left (Real.sqrt_le_sqrt (sub_le_sub_left
    (div_le_div_of_nonneg_left (by norm_num) hV1pos h12) _)) _

/-- For `V ≥ 2`, `κ_eff (2 - κ_eff) = 2 / V`. -/
private theorem effectiveCurvature_mul_complement {V : ℝ} (hV : 2 ≤ V) :
    effectiveCurvature V * (2 - effectiveCurvature V) = 2 / V := by
  have hVpos : 0 < V := by linarith
  rw [effectiveCurvature]
  set s := Real.sqrt (1 - 2 / V)
  have hsq : s ^ 2 = 1 - 2 / V :=
    Real.sq_sqrt (sub_nonneg.mpr ((div_le_one hVpos).mpr hV))
  nlinarith only [hsq]

/-- Equation (S39) for a single variance `V ≥ 2`:
`1 / (2 V) = κ_eff (2 - κ_eff) / 4`. -/
theorem one_div_two_mul_eq_effectiveCurvature {V : ℝ} (hV : 2 ≤ V) :
    1 / (2 * V) = effectiveCurvature V * (2 - effectiveCurvature V) / 4 := by
  rw [effectiveCurvature_mul_complement hV]
  ring

/-- Equation (S36): for `V ≥ 2`, `V = 2 / (κ_eff (2 - κ_eff))`. -/
theorem eq_two_div_effectiveCurvature {V : ℝ} (hV : 2 ≤ V) :
    V = 2 / (effectiveCurvature V * (2 - effectiveCurvature V)) := by
  rw [effectiveCurvature_mul_complement hV, div_div_eq_mul_div]
  ring

/-- Equation (S34): for `0 ≤ r < 1`, the series `∑_j 2 (r²)^j` sums to
`2 / (1 - r²)`. -/
theorem hasSum_two_mul_geometric_sq {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun j : ℕ => 2 * (r ^ 2) ^ j) (2 / (1 - r ^ 2)) := by
  have hsq : r ^ 2 < 1 := (sq_lt_one_iff₀ h0).2 h1
  simpa only [div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one (sq_nonneg r) hsq).mul_left 2

/-- For `r ≥ 0`, substituting `2 / (1 - r²)` in the effective curvature formula gives
`1 - r`. -/
theorem effectiveCurvature_equivalentBond {r : ℝ} (h0 : 0 ≤ r) :
    effectiveCurvature (2 / (1 - r ^ 2)) = 1 - r := by
  rw [effectiveCurvature, div_div_eq_mul_div, mul_div_cancel_left₀ _ two_ne_zero,
    sub_sub_cancel, Real.sqrt_sq h0]

end GraphStability
