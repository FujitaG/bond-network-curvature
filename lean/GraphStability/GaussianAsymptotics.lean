import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithm of a Gaussian bound, divided by `Θ²` (Theorem 3)
-/

open Filter Topology

namespace GraphStability

/-- For `C > 0`, `log (C exp(a (Θ + shift)²)) / Θ² → a` as `Θ → ∞`. -/
theorem tendsto_log_mul_exp_quadratic (C a shift : ℝ) (hC : 0 < C) :
    Tendsto (fun Θ : ℝ => Real.log (C * Real.exp (a * (Θ + shift) ^ 2)) / Θ ^ 2)
      atTop (𝓝 a) := by
  have hinv : Tendsto (fun Θ : ℝ => Θ⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hlim : Tendsto
      (fun Θ : ℝ => Real.log C * (Θ⁻¹) ^ 2 + a * (1 + shift * Θ⁻¹) ^ 2)
      atTop (𝓝 a) := by
    convert (tendsto_const_nhds.mul (hinv.pow 2)).add
      (tendsto_const_nhds.mul
        ((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).pow 2)) using 1
    simp
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Θ hΘ
  rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]
  field_simp

/-- Suppose `C > 0`, each `K n > 0`, and `A n → a`. For each `ε > 0` there is `Θ₀ > 0`
such that, for every `Θ ≥ Θ₀`, every `y` satisfying `C exp(a Θ²) ≤ y` and
`y ≤ K n exp(A n (Θ + 2)²)` for all `n` satisfies `|log y / Θ² - a| < ε`. -/
theorem uniform_log_of_quadratic_bounds (a C : ℝ)
    (A K : ℕ → ℝ) (hC : 0 < C) (hK : ∀ n, 0 < K n)
    (hA : Tendsto A atTop (𝓝 a)) :
    ∀ ε > 0, ∃ Θ₀ : ℝ, 0 < Θ₀ ∧ ∀ Θ ≥ Θ₀, ∀ y : ℝ,
      C * Real.exp (a * Θ ^ 2) ≤ y →
      (∀ n, y ≤ K n * Real.exp (A n * (Θ + 2) ^ 2)) →
      |Real.log y / Θ ^ 2 - a| < ε := by
  intro ε hε
  have hl := tendsto_log_mul_exp_quadratic C a 0 hC
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hA).2 (a + ε) (by linarith)).exists
  have hu := tendsto_log_mul_exp_quadratic (K n) (A n) 2 (hK n)
  obtain ⟨Θ₀, h⟩ := eventually_atTop.1 <| (eventually_gt_atTop (0 : ℝ)).and
    (((tendsto_order.1 hl).1 (a - ε) (by linarith)).and
      ((tendsto_order.1 hu).2 (a + ε) hn))
  refine ⟨Θ₀, (h Θ₀ le_rfl).1, ?_⟩
  intro Θ hΘ y hlower hupper
  obtain ⟨_, hlΘ, huΘ⟩ := h Θ hΘ
  have hpos := mul_pos hC (Real.exp_pos (a * Θ ^ 2))
  have hlo := div_le_div_of_nonneg_right (Real.log_le_log hpos hlower) (sq_nonneg Θ)
  have hup := div_le_div_of_nonneg_right
    (Real.log_le_log (hpos.trans_le hlower) (hupper n)) (sq_nonneg Θ)
  simp only [add_zero] at hlΘ
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end GraphStability
