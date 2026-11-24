import GraphStability.GaussianTail
import GraphStability.Variance

/-!
# Past and fresh noise over an interval of `T` rounds (Lemma T2.5)

An edge difference splits into a part determined by past rounds and an
independent Gaussian contribution from the next interval of `T` rounds. The
probability bounds assume `σ > 0`, `θ > 0`, and `V_T(e) > 0`.
-/

noncomputable section

open MeasureTheory

namespace GraphStability

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : MarkovKernel V} {σ : ℝ} {Ω : Type*}
  [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- The contribution to `D_{n+T}(u, v)` from the noise of rounds
`1, …, n`. -/
def pastPart (proc : GaussianAveragingProcess P σ Ω) (u v : V) (n T : ℕ) :
    Ω → ℝ :=
  fun ω => ∑ s ∈ Finset.Icc 1 n, ∑ z,
    differenceRow P u v (n + T - s) z * proc.ξ s z ω

/-- The contribution to `D_{n+T}(u, v)` from the noise of rounds
`n + 1, …, n + T`. -/
def freshPart (proc : GaussianAveragingProcess P σ Ω) (u v : V) (n T : ℕ) :
    Ω → ℝ :=
  fun ω => ∑ s ∈ Finset.Icc (n + 1) (n + T), ∑ z,
    differenceRow P u v (n + T - s) z * proc.ξ s z ω

/-- Equation (S56): the edge difference is the sum of its past and fresh parts. -/
theorem edgeDiff_eq_past_add_fresh (proc : GaussianAveragingProcess P σ Ω)
    (u v : V) (n T : ℕ) (ω : Ω) :
    proc.f (n + T) u ω - proc.f (n + T) v ω
      = pastPart proc u v n T ω + freshPart proc u v n T ω := by
  rw [edgeDiff_eq_sum_rounds]
  simpa only [pastPart, freshPart, Finset.Ico_add_one_right_eq_Icc] using
    (Finset.sum_Ico_consecutive
      (fun s => ∑ z, differenceRow P u v (n + T - s) z * proc.ξ s z ω)
      (m := 1) (n := n + 1) (k := n + T + 1) (by omega) (by omega)).symm

/-- The number `p_T(e)` of equation (S54), as a function of `v` and `Θ`. For
`v = V_T(e) > 0`, positive `σ` and `θ`, and `Θ = θ/σ`, it is a lower bound
on the probability that the fresh noise of `T` rounds brings the edge
difference to the threshold, whatever the past part. -/
def blockProbability (v Θ : ℝ) : ℝ :=
  2 / Real.sqrt (2 * Real.pi * v) * Real.exp (-(Θ + 2) ^ 2 / (2 * v))

/-- `blockProbability v Θ` is positive for `v > 0`. -/
theorem blockProbability_pos {v : ℝ} (hv : 0 < v) (Θ : ℝ) : 0 < blockProbability v Θ := by
  unfold blockProbability
  positivity

/-- For any `a` with `|a| = θ + σ`, the probability that
`|freshPart proc u v n T - a| ≤ σ` is at least `p_T(e)`. -/
theorem freshPart_interval_probability (proc : GaussianAveragingProcess P σ Ω) (hσ : 0 < σ)
    {u v : V} (n : ℕ) {T : ℕ} (hV : 0 < normalizedVariance P u v T) {θ a : ℝ}
    (ha : |a| = θ + σ) :
    ENNReal.ofReal (blockProbability (normalizedVariance P u v T) (θ / σ)) ≤
      volume {ω | |freshPart proc u v n T ω - a| ≤ σ} := by
  set Vt := normalizedVariance P u v T
  have hVpos : 0 < σ ^ 2 * Vt := by positivity
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    (gaussian_interval_probability_lower hVpos a σ hσ.le (noiseBlock_gaussian proc u v n T))
  have hs : Real.sqrt (2 * Real.pi * (σ ^ 2 * Vt)) = σ * Real.sqrt (2 * Real.pi * Vt) := by
    rw [show 2 * Real.pi * (σ ^ 2 * Vt) = σ ^ 2 * (2 * Real.pi * Vt) by ring,
      Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
  have hpos : 0 < Real.sqrt (2 * Real.pi * Vt) := by positivity
  unfold blockProbability
  rw [ha, hs, show θ + σ + σ = θ + 2 * σ by ring]
  congr 1
  · field_simp
  · congr 1
    field_simp

/-- The fresh part is at least `θ` with probability at least `p_T(e)`. -/
theorem freshPart_ge_probability (proc : GaussianAveragingProcess P σ Ω) (hσ : 0 < σ)
    {u v : V} (n : ℕ) {T : ℕ} (hV : 0 < normalizedVariance P u v T) {θ : ℝ} (hθ : 0 < θ) :
    ENNReal.ofReal (blockProbability (normalizedVariance P u v T) (θ / σ)) ≤
      volume {ω | θ ≤ freshPart proc u v n T ω} := by
  refine (freshPart_interval_probability proc hσ n hV (a := θ + σ)
    (abs_of_pos (by linarith))).trans (measure_mono fun ω hω => ?_)
  simp only [Set.mem_setOf_eq, abs_le] at hω ⊢
  linarith [hω.1]

/-- The fresh part is at most `-θ` with probability at least `p_T(e)`. -/
theorem freshPart_le_neg_probability (proc : GaussianAveragingProcess P σ Ω) (hσ : 0 < σ)
    {u v : V} (n : ℕ) {T : ℕ} (hV : 0 < normalizedVariance P u v T) {θ : ℝ} (hθ : 0 < θ) :
    ENNReal.ofReal (blockProbability (normalizedVariance P u v T) (θ / σ)) ≤
      volume {ω | freshPart proc u v n T ω ≤ -θ} := by
  refine (freshPart_interval_probability proc hσ n hV (a := -(θ + σ))
    (by rw [abs_neg, abs_of_pos (by linarith)])).trans (measure_mono fun ω hω => ?_)
  simp only [Set.mem_setOf_eq, abs_le] at hω ⊢
  linarith [hω.2]

omit [MeasureSpace Ω] in
/-- At each sample point, `c ≥ 0` and `g ≥ θ`, or `c < 0` and `g ≤ -θ`, implies
`|c + g| ≥ θ`. -/
theorem signSplit_subset (c g : Ω → ℝ) (θ : ℝ) :
    ({ω | 0 ≤ c ω} ∩ {ω | θ ≤ g ω}) ∪ ({ω | c ω < 0} ∩ {ω | g ω ≤ -θ})
      ⊆ {ω | θ ≤ |c ω + g ω|} := by
  rintro ω (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
    simp only [Set.mem_setOf_eq] at h1 h2 ⊢
  · linarith [le_abs_self (c ω + g ω)]
  · linarith [neg_le_abs (c ω + g ω)]

/-- For every real number `c`, the probability that
`|c + freshPart proc u v n T| ≥ θ` is at least `p_T(e)`. -/
theorem abs_add_freshPart_probability (proc : GaussianAveragingProcess P σ Ω) (hσ : 0 < σ)
    {u v : V} (n : ℕ) {T : ℕ} (hV : 0 < normalizedVariance P u v T) {θ : ℝ} (hθ : 0 < θ)
    (c : ℝ) :
    ENNReal.ofReal (blockProbability (normalizedVariance P u v T) (θ / σ)) ≤
      volume {ω | θ ≤ |c + freshPart proc u v n T ω|} := by
  rcases le_or_gt 0 c with hc | hc
  · exact (freshPart_ge_probability proc hσ n hV hθ).trans (measure_mono fun ω hω =>
      signSplit_subset (fun _ => c) (freshPart proc u v n T) θ (Or.inl ⟨hc, hω⟩))
  · exact (freshPart_le_neg_probability proc hσ n hV hθ).trans (measure_mono fun ω hω =>
      signSplit_subset (fun _ => c) (freshPart proc u v n T) θ (Or.inr ⟨hc, hω⟩))

end GraphStability
