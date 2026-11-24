import GraphStability.EffectiveLifetime
import GraphStability.LifetimeUpper
import GraphStability.GaussianAsymptotics

/-!
# Exponential growth rate of the mean lifetime (Theorem 3)

For a fixed interval length `T`, the logarithm of the upper bound of Lemma T2.5,
divided by `Θ²`, tends to `1/(2 V_T(e))`. Choosing an edge of maximum
limiting variance and letting `T` grow brings this limit to the `1/(2 M_G)`
of the lower bound of Theorem 2.
-/

open Filter Topology MeasureTheory
open scoped ENNReal

namespace GraphStability

universe uΩ

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {P : MarkovKernel V} {σ : ℝ} {Ω : Type*}
  [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- For `σ > 0` and `θ > 0`, the mean lifetime on a graph with an edge is finite. -/
theorem meanLifetime_ne_top (proc : GaussianAveragingProcess P σ Ω) (hσ : 0 < σ)
    {θ : ℝ} (hθ : 0 < θ) {u v : V} (hadj : G.Adj u v) :
    meanLifetime G θ proc ≠ ⊤ := by
  have hV : 0 < normalizedVariance P u v 1 := normalizedVariance_pos P hadj.ne le_rfl
  refine ne_top_of_le_ne_top ?_
    (meanLifetime_upper_bound proc hσ hθ hadj (T := 1) le_rfl)
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (blockProbability_pos hV _)).ne')

/-- Equation (S60): for `σ > 0`, `Θ > 0`, an edge `(u, v)`, and `T ≥ 1`, the
upper bound of Lemma T2.5 as a real number, in terms of `Θ = θ/σ`. -/
theorem meanLifetime_toReal_upper_normalized (proc : GaussianAveragingProcess P σ Ω)
    (hσ : 0 < σ)
    {Θ : ℝ} (hΘ : 0 < Θ) {u v : V} (hadj : G.Adj u v)
    {T : ℕ} (hT : 1 ≤ T) :
    (meanLifetime G (σ * Θ) proc).toReal ≤
      ((T : ℝ) * Real.sqrt (2 * Real.pi * normalizedVariance P u v T) / 2) *
      Real.exp ((1 / (2 * normalizedVariance P u v T)) * (Θ + 2) ^ 2) := by
  have hvar : 0 < normalizedVariance P u v T := normalizedVariance_pos P hadj.ne hT
  set Vt := normalizedVariance P u v T
  have hp : 0 < blockProbability Vt Θ := blockProbability_pos hvar Θ
  have hu := meanLifetime_upper_bound proc hσ (mul_pos hσ hΘ) hadj hT
  rw [mul_div_cancel_left₀ Θ hσ.ne'] at hu
  have hfin : (T : ℝ≥0∞) * (ENNReal.ofReal (blockProbability Vt Θ))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hp).ne')
  have hreal := ENNReal.toReal_mono hfin hu
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hp.le] at hreal
  refine hreal.trans (le_of_eq ?_)
  unfold blockProbability
  rw [mul_inv_rev, inv_div, ← Real.exp_neg,
    show -(-(Θ + 2) ^ 2 / (2 * Vt)) = (1 / (2 * Vt)) * (Θ + 2) ^ 2 by ring]
  ring

/-- Theorem 3: for a finite graph with an edge and a kernel for which the
series defining `V_∞(e)` converges on every edge, `log 𝔼[τ_{σ Θ}] / Θ²` is
within `ε` of `1 / (2 M_G)` for all `Θ ≥ Θ₀`, uniformly in `σ > 0`, the
process, and its probability space. -/
theorem meanLifetime_rate_uniform [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty)
    (hs : ∀ u v, G.Adj u v →
      Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) :
    ∀ ε > 0, ∃ Θ₀ : ℝ, ∀ Θ ≥ Θ₀,
      ∀ {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
        {σ : ℝ}, 0 < σ → ∀ (proc : GaussianAveragingProcess P σ Ω),
      |Real.log (meanLifetime G (σ * Θ) proc).toReal / Θ ^ 2 -
        1 / (2 * maxLimitingVariance G P hE)| < ε := by
  obtain ⟨u, v, hadj, hmax⟩ := exists_edge_maxLimitingVariance (P := P) hE
  have hbound := fun t x y (hxy : G.Adj x y) => normalizedVariance_le_max hE hs t hxy
  have hlimit := hmax ▸ normalizedVariance_tendsto P u v (hs u v hadj)
  generalize maxLimitingVariance G P hE = M at hbound hlimit ⊢
  let C : ℝ := 1 / (4 * (G.edgeFinset.card : ℝ))
  let A : ℕ → ℝ := fun n => 1 / (2 * normalizedVariance P u v (n + 1))
  let K : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) *
    Real.sqrt (2 * Real.pi * normalizedVariance P u v (n + 1)) / 2
  have hC : 0 < C := by
    have hcard : 0 < (G.edgeFinset.card : ℝ) := Nat.cast_pos.mpr hE.card_pos
    exact one_div_pos.mpr (mul_pos (by norm_num) hcard)
  have hvpos (n : ℕ) : 0 < normalizedVariance P u v (n + 1) :=
    normalizedVariance_pos P hadj.ne (by omega)
  have hM : 0 < M := (hvpos 0).trans_le (hbound 1 u v hadj)
  have hK (n : ℕ) : 0 < K n := by have := hvpos n; dsimp [K]; positivity
  have hA : Tendsto A atTop (𝓝 (1 / (2 * M))) :=
    tendsto_const_nhds.div
      (tendsto_const_nhds.mul (hlimit.comp (tendsto_add_atTop_nat 1))) (by positivity)
  intro ε hε
  obtain ⟨Θ₀, hΘ₀, h⟩ :=
    uniform_log_of_quadratic_bounds (1 / (2 * M)) C A K hC hK hA ε hε
  refine ⟨Θ₀, ?_⟩
  intro Θ hΘ Ω _ _ σ hσ proc
  have hΘpos := hΘ₀.trans_le hΘ
  have hθ := mul_pos hσ hΘpos
  refine h Θ hΘ _ ?_ ?_
  · have hl := meanLifetime_lower_bound proc hθ hE hbound
    rw [mul_div_cancel_left₀ Θ hσ.ne'] at hl
    have hreal := (ENNReal.ofReal_le_iff_le_toReal
      (meanLifetime_ne_top proc hσ hθ hadj)).1 hl
    rw [show Θ ^ 2 / (2 * M) = 1 / (2 * M) * Θ ^ 2 by ring] at hreal
    simpa only [C, div_eq_mul_inv, one_mul, mul_comm] using hreal
  · intro n
    exact meanLifetime_toReal_upper_normalized proc hσ hΘpos hadj (T := n + 1) (by omega)

end GraphStability
