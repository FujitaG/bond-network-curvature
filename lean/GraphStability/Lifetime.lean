import GraphStability.Variance

/-!
# The lifetime and its mean (equations (S15) and (S51))

Because a break may never occur, the lifetime takes values in `ℕ∞` and its
mean in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GraphStability

variable {V Ω : Type*} [Fintype V]
  [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
  {G : SimpleGraph V} {P : MarkovKernel V} {σ : ℝ}

/-- The lifetime `τ_θ`: the first round at which some edge difference reaches
the threshold `θ`, and `⊤` if no such round occurs. Because `f₀ = 0`, no break
occurs at round `0` when `θ > 0` (`lifetime_le_iff_of_pos`). -/
def lifetime (G : SimpleGraph V) (θ : ℝ)
    (proc : GaussianAveragingProcess P σ Ω) : Ω → ℕ∞ :=
  fun ω => ⨅ (n : ℕ) (_ : ∃ u v, G.Adj u v ∧ θ ≤ |proc.f n u ω - proc.f n v ω|), (n : ℕ∞)

/-- A break by round `T` occurs if and only if some edge difference reaches `θ`
at some round `t ≤ T`. -/
theorem lifetime_le_iff (proc : GaussianAveragingProcess P σ Ω)
    (θ : ℝ) (T : ℕ) (ω : Ω) :
    lifetime G θ proc ω ≤ T ↔
      ∃ t ≤ T, ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω| := by
  rw [← ENat.lt_coe_add_one_iff]
  simp only [lifetime, iInf_lt_iff, ENat.lt_coe_add_one_iff, Nat.cast_le, exists_prop, and_comm]

/-- The event of a break by round `T` is the union of the per-round breaking
events for `t ≤ T`. -/
theorem lifetime_le_eq_union (proc : GaussianAveragingProcess P σ Ω)
    (θ : ℝ) (T : ℕ) :
    {ω | lifetime G θ proc ω ≤ T} =
      ⋃ t ∈ Finset.range (T + 1),
        {ω | ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω|} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
    lifetime_le_iff, Nat.lt_add_one_iff]

/-- Survival past round `t` is measurable with respect to every σ-algebra for
which the values of rounds `0, …, t` are measurable. -/
theorem measurableSet_lifetime_gt_of_measurable (proc : GaussianAveragingProcess P σ Ω)
    (θ : ℝ) (t : ℕ) {m : MeasurableSpace Ω} (hm : ∀ n ≤ t, ∀ x, Measurable[m] (proc.f n x)) :
    MeasurableSet[m] {ω | t < lifetime G θ proc ω} := by
  have hbreak : MeasurableSet[m] {ω | lifetime G θ proc ω ≤ t} := by
    rw [lifetime_le_eq_union]
    refine Finset.measurableSet_biUnion _ fun n hn => ?_
    have hn' : n ≤ t := Finset.mem_range_succ_iff.mp hn
    simp only [Set.setOf_exists]
    refine MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun v => ?_
    exact (MeasurableSet.const _).inter (((hm n hn' u).sub (hm n hn' v)).abs measurableSet_Ici)
  simpa only [Set.compl_setOf, not_le] using hbreak.compl

/-- The survival events are measurable. -/
theorem measurableSet_lifetime_gt (proc : GaussianAveragingProcess P σ Ω)
    (θ : ℝ) (t : ℕ) :
    MeasurableSet {ω | t < lifetime G θ proc ω} :=
  measurableSet_lifetime_gt_of_measurable proc θ t fun n _ x => measurable_f proc n x

/-- For `θ > 0`, a break by round `T` occurs if and only if some edge
difference reaches `θ` at some round `1 ≤ t ≤ T`. -/
theorem lifetime_le_iff_of_pos (proc : GaussianAveragingProcess P σ Ω)
    {θ : ℝ} (hθ : 0 < θ) (T : ℕ) (ω : Ω) :
    lifetime G θ proc ω ≤ T ↔
      ∃ t, 1 ≤ t ∧ t ≤ T ∧
        ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω| := by
  rw [lifetime_le_iff]
  constructor
  · rintro ⟨t, htT, u, v, huv, h⟩
    refine ⟨t, Nat.pos_of_ne_zero ?_, htT, u, v, huv, h⟩
    rintro rfl
    simp only [proc.f_zero, Pi.zero_apply, sub_self, abs_zero] at h
    exact absurd h (not_le.mpr hθ)
  · rintro ⟨t, _, htT, h⟩
    exact ⟨t, htT, h⟩

/-- For `θ > 0`, the event of a break by round `T` is the union of the
per-round breaking events over `1 ≤ t ≤ T`. -/
theorem lifetime_le_eq_union_of_pos
    (proc : GaussianAveragingProcess P σ Ω) {θ : ℝ} (hθ : 0 < θ) (T : ℕ) :
    {ω | lifetime G θ proc ω ≤ T} =
      ⋃ t ∈ Finset.Icc 1 T,
        {ω | ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω|} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop,
    lifetime_le_iff_of_pos proc hθ, and_assoc]

/-- The mean lifetime, defined as the sum `∑_t ℙ(τ_θ > t)` of the survival
probabilities. It equals the expectation of the lifetime
(`meanLifetime_eq_lintegral`). -/
def meanLifetime (G : SimpleGraph V) (θ : ℝ) (proc : GaussianAveragingProcess P σ Ω) : ℝ≥0∞ :=
  ∑' t : ℕ, volume {ω | t < lifetime G θ proc ω}

/-- For `θ > 0`, the mean lifetime is at least `1`. -/
theorem meanLifetime_ge_one (proc : GaussianAveragingProcess P σ Ω)
    {θ : ℝ} (hθ : 0 < θ) :
    1 ≤ meanLifetime G θ proc := by
  have hzero : {ω | (0 : ℕ) < lifetime G θ proc ω} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, ← not_le,
      lifetime_le_iff_of_pos proc hθ]
    rintro ⟨t, ht1, ht0, -⟩
    omega
  simpa only [hzero, measure_univ, meanLifetime] using
    (ENNReal.le_tsum (f := fun t : ℕ => volume {ω | (t : ℕ∞) < lifetime G θ proc ω}) 0)

/-- Every extended natural number `n : ℕ∞` equals the sum of indicators of all
natural numbers strictly below `n`. -/
theorem enat_cast_eq_sum_indicators (n : ℕ∞) :
    (n : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < n then (1 : ℝ≥0∞) else 0 := by
  cases n using ENat.recTopCoe with
  | top => simp
  | coe n =>
      simp only [ENat.toENNReal_coe, ENat.coe_lt_coe]
      simpa [Set.indicator, nsmul_eq_mul] using
        (sum_eq_tsum_indicator (fun _ : ℕ => (1 : ℝ≥0∞)) (Finset.range n))

/-- The mean lifetime, defined by its tail sum, is the expectation of the lifetime. -/
theorem meanLifetime_eq_lintegral (proc : GaussianAveragingProcess P σ Ω) (θ : ℝ) :
    meanLifetime G θ proc = ∫⁻ ω, (lifetime G θ proc ω : ℝ≥0∞) := by
  let event := fun t : ℕ => {ω | t < lifetime G θ proc ω}
  have hm : ∀ t, MeasurableSet (event t) :=
    measurableSet_lifetime_gt proc θ
  calc
    meanLifetime G θ proc = ∑' t, ∫⁻ ω, (event t).indicator (1 : Ω → ℝ≥0∞) ω :=
      tsum_congr fun t => (lintegral_indicator_one (hm t)).symm
    _ = ∫⁻ ω, ∑' t, (event t).indicator (1 : Ω → ℝ≥0∞) ω :=
      (lintegral_tsum (fun t => (measurable_const.indicator (hm t)).aemeasurable)).symm
    _ = ∫⁻ ω, (lifetime G θ proc ω : ℝ≥0∞) := by
      apply lintegral_congr
      intro ω
      simpa [event, Set.indicator] using
        (enat_cast_eq_sum_indicators (lifetime G θ proc ω)).symm

end GraphStability
