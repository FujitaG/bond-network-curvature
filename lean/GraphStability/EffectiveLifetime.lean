import GraphStability.LifetimeLower
import GraphStability.Extrema

/-!
# Lifetime bounds in terms of `M_G` and effective curvature (Theorem 2, equation (S53))

Throughout, `G` has an edge and the series defining `V_∞(e)` converges on every
edge. If every edge has effective curvature at least `κ₀`, then
`1 / (2 M_G) ≥ κ₀ (2 - κ₀) / 4`. Substituting this inequality in Theorem 2 gives
(S53).
-/

namespace GraphStability

open MeasureTheory

variable {V Ω : Type*} [Fintype V] [DecidableEq V]
  [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
  {G : SimpleGraph V} [DecidableRel G.Adj] {P : MarkovKernel V} {σ : ℝ}
  (hE : G.edgeFinset.Nonempty)
  (hs : ∀ u v, G.Adj u v → Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2))

include hE hs

/-- Equation (S48): `V_t(e) ≤ M_G`, because `V_t(e) ≤ V_∞(e) ≤ M_G`. -/
theorem normalizedVariance_le_max (t : ℕ) {u v : V} (huv : G.Adj u v) :
    normalizedVariance P u v t ≤ maxLimitingVariance G P hE :=
  (normalizedVariance_le_limitingVariance P u v (hs u v huv) t).trans
    (limitingVariance_le_max hE huv)

/-- Theorem 2, equation (S47): for `θ > 0`,
`ℙ(τ_θ ≤ T) ≤ 2 |E| T exp(-Θ² / (2 M_G))` with `Θ = θ/σ`. -/
theorem lifetime_probability_le_of_maxLimitingVariance
    (proc : GaussianAveragingProcess P σ Ω) {θ : ℝ} (hθ : 0 < θ) (T : ℕ) :
    volume {ω | lifetime G θ proc ω ≤ T} ≤
      ENNReal.ofReal (2 * G.edgeFinset.card * T *
        Real.exp (-(θ / σ) ^ 2 / (2 * maxLimitingVariance G P hE))) :=
  lifetime_probability_le proc hθ T fun _ _ huv => normalizedVariance_le_max hE hs T huv

/-- Theorem 2, equation (S46): for `θ > 0`,
`𝔼[τ_θ] ≥ exp(Θ² / (2 M_G)) / (4 |E|)` with `Θ = θ/σ`. -/
theorem meanLifetime_lower_of_maxLimitingVariance
    (proc : GaussianAveragingProcess P σ Ω) {θ : ℝ} (hθ : 0 < θ) :
    ENNReal.ofReal (Real.exp ((θ / σ) ^ 2 / (2 * maxLimitingVariance G P hE)) /
      (4 * G.edgeFinset.card)) ≤ meanLifetime G θ proc :=
  meanLifetime_lower_bound proc hθ hE fun t _ _ huv => normalizedVariance_le_max hE hs t huv

/-- If `κ₀ ≤ κ_eff(e)` for every edge `e`, then
`κ₀ (2 - κ₀) Θ² / 4 ≤ Θ² / (2 M_G)`. -/
theorem exponent_le_of_effectiveCurvature_ge {κ₀ : ℝ}
    (hfloor : ∀ u v, G.Adj u v → κ₀ ≤ effectiveCurvature (limitingVariance P u v))
    (Θ : ℝ) :
    κ₀ * (2 - κ₀) * Θ ^ 2 / 4 ≤ Θ ^ 2 / (2 * maxLimitingVariance G P hE) := by
  obtain ⟨u, v, huv, hmax⟩ := exists_edge_maxLimitingVariance (P := P) hE
  have hV : 2 ≤ limitingVariance P u v := limitingVariance_ge_two P huv.ne (hs u v huv)
  have hk := hfloor u v huv
  have hk1 := effectiveCurvature_le_one (limitingVariance P u v)
  have hrate : κ₀ * (2 - κ₀) / 4 ≤ 1 / (2 * maxLimitingVariance G P hE) := by
    rw [← hmax, one_div_two_mul_eq_effectiveCurvature hV]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk)
      (show 0 ≤ 2 - effectiveCurvature (limitingVariance P u v) - κ₀ by linarith)]
  simpa only [div_mul_eq_mul_div₀, one_mul] using
    mul_le_mul_of_nonneg_right hrate (sq_nonneg Θ)

/-- Equation (S47) with the exponent of (S53): if `θ > 0` and `κ₀ ≤ κ_eff(e)`
for every edge `e`, then `ℙ(τ_θ ≤ T) ≤ 2 |E| T exp(-κ₀ (2 - κ₀) Θ² / 4)`. -/
theorem lifetime_probability_le_of_effectiveCurvature
    (proc : GaussianAveragingProcess P σ Ω) {θ κ₀ : ℝ} (hθ : 0 < θ)
    (hfloor : ∀ u v, G.Adj u v → κ₀ ≤ effectiveCurvature (limitingVariance P u v)) (T : ℕ) :
    volume {ω | lifetime G θ proc ω ≤ T} ≤
      ENNReal.ofReal (2 * G.edgeFinset.card * T *
        Real.exp (-κ₀ * (2 - κ₀) * (θ / σ) ^ 2 / 4)) := by
  refine (lifetime_probability_le_of_maxLimitingVariance hE hs proc hθ T).trans
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)))
  simpa only [neg_mul, neg_div, neg_le_neg_iff] using
    exponent_le_of_effectiveCurvature_ge hE hs hfloor (θ / σ)

/-- Equation (S53): if `θ > 0` and `κ₀ ≤ κ_eff(e)` for every edge `e`, then
`𝔼[τ_θ] ≥ exp(κ₀ (2 - κ₀) Θ² / 4) / (4 |E|)`. -/
theorem meanLifetime_lower_of_effectiveCurvature
    (proc : GaussianAveragingProcess P σ Ω) {θ κ₀ : ℝ} (hθ : 0 < θ)
    (hfloor : ∀ u v, G.Adj u v → κ₀ ≤ effectiveCurvature (limitingVariance P u v)) :
    ENNReal.ofReal (Real.exp (κ₀ * (2 - κ₀) * (θ / σ) ^ 2 / 4) / (4 * G.edgeFinset.card)) ≤
      meanLifetime G θ proc :=
  (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (Real.exp_le_exp.mpr (exponent_le_of_effectiveCurvature_ge hE hs hfloor (θ / σ)))
    (by positivity))).trans (meanLifetime_lower_of_maxLimitingVariance hE hs proc hθ)

end GraphStability
