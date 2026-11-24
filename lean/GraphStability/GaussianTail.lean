import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian

/-!
# Two-sided Gaussian tail (Lemma T2.4) and a lower bound on the probability of an interval

The interval bound specializes to equation (S57) in Lemma T2.5.
-/

open MeasureTheory ProbabilityTheory

namespace GraphStability

/-- Lemma T2.4: a centred Gaussian variable `Z` with variance `v` satisfies
`ℙ(|Z| ≥ θ) ≤ 2 exp(-θ² / (2 v))` for every `θ > 0`. -/
theorem gaussian_tail_bound {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {Z : Ω → ℝ} {v : NNReal} (hZ : Measure.map Z volume = gaussianReal 0 v)
    {θ : ℝ} (hθ : 0 < θ) :
    volume.real {ω | θ ≤ |Z ω|} ≤ 2 * Real.exp (-θ ^ 2 / (2 * v)) := by
  have hmgf (t : ℝ) : mgf Z volume t = Real.exp (v * t ^ 2 / 2) := by
    simpa using mgf_gaussianReal hZ t
  have hsub : HasSubgaussianMGF Z v volume :=
    ⟨fun t => mgf_pos_iff.mp (by rw [hmgf]; exact Real.exp_pos _), fun t => (hmgf t).le⟩
  have hsplit : {ω | θ ≤ |Z ω|} ⊆ {ω | θ ≤ Z ω} ∪ {ω | θ ≤ (-Z) ω} := fun ω (hω : θ ≤ |Z ω|) =>
    (le_abs.mp hω : θ ≤ Z ω ∨ θ ≤ -Z ω)
  calc volume.real {ω | θ ≤ |Z ω|}
      ≤ volume.real ({ω | θ ≤ Z ω} ∪ {ω | θ ≤ (-Z) ω}) := measureReal_mono hsplit
    _ ≤ volume.real {ω | θ ≤ Z ω} + volume.real {ω | θ ≤ (-Z) ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-θ ^ 2 / (2 * v)) + Real.exp (-θ ^ 2 / (2 * v)) :=
        add_le_add (hsub.measure_ge_le hθ.le) (hsub.neg.measure_ge_le hθ.le)
    _ = 2 * Real.exp (-θ ^ 2 / (2 * v)) := (two_mul _).symm

/-- For `Z ~ N(0, v)` with `v > 0` and `r ≥ 0`, the probability that `|Z - a| ≤ r` is at
least `(2 r / √(2 π v)) exp(-(|a| + r)² / (2 v))`. -/
theorem gaussian_interval_probability_lower {Ω : Type*} [MeasureSpace Ω]
    {Z : Ω → ℝ} {v : ℝ} (hv : 0 < v) (a r : ℝ) (hr : 0 ≤ r)
    (hZ : Measure.map Z volume = gaussianReal 0 v.toNNReal) :
    ENNReal.ofReal ((2 * r) / Real.sqrt (2 * Real.pi * v) *
        Real.exp (-(|a| + r) ^ 2 / (2 * v))) ≤
      volume {ω | |Z ω - a| ≤ r} := by
  have hvar : v.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hv).ne'
  have hpdf (x : ℝ) : gaussianPDFReal 0 v.toNNReal x =
      (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-x ^ 2 / (2 * v)) := by
    simp only [gaussianPDFReal, Real.coe_toNNReal _ hv.le, sub_zero, one_div]
  let densityFloor : ℝ :=
    (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(|a| + r) ^ 2 / (2 * v))
  have hdensity (x : ℝ) (hx : x ∈ Set.Icc (a - r) (a + r)) :
      densityFloor ≤ gaussianPDFReal 0 v.toNNReal x := by
    have hdist : |x - a| ≤ r := by
      simpa only [← Real.closedBall_eq_Icc, Metric.mem_closedBall, Real.dist_eq] using hx
    have habs : |x| ≤ |a| + r := by linarith [abs_sub_abs_le_abs_sub x a]
    have hsq : x ^ 2 ≤ (|a| + r) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) habs 2
    rw [hpdf]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)
  have hintegral :
      (2 * r) / Real.sqrt (2 * Real.pi * v) * Real.exp (-(|a| + r) ^ 2 / (2 * v)) ≤
        ∫ x in Set.Icc (a - r) (a + r), gaussianPDFReal 0 v.toNNReal x := by
    calc
      _ = ∫ _x in Set.Icc (a - r) (a + r), densityFloor := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
        dsimp [densityFloor]
        ring
      _ ≤ _ := setIntegral_mono_on (integrableOn_const (by simp))
        (integrable_gaussianPDFReal _ _).integrableOn measurableSet_Icc hdensity
  have hZ_meas : AEMeasurable Z volume := aemeasurable_of_map_neZero (by rw [hZ]; infer_instance)
  have hevent : {ω | |Z ω - a| ≤ r} = Z ⁻¹' Set.Icc (a - r) (a + r) :=
    congrArg (fun s : Set ℝ => Z ⁻¹' s) (Real.closedBall_eq_Icc (x := a) (r := r))
  rw [hevent, ← Measure.map_apply_of_aemeasurable hZ_meas measurableSet_Icc, hZ,
    gaussianReal_apply_eq_integral 0 hvar]
  exact ENNReal.ofReal_le_ofReal hintegral

end GraphStability
