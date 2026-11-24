import GraphStability.Process

/-!
# The variance of an edge difference (Lemma T2.1)

The vertex values are sums of the past noise weighted by powers of `P`. Each
edge difference is therefore Gaussian, with variance `σ²` times the sum of the
squared Euclidean norms of the rows `q_eᵀ P^j`.
-/

namespace GraphStability

open MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Markov kernel as a real matrix. -/
def kernelMatrix (P : MarkovKernel V) : Matrix V V ℝ :=
  Matrix.of fun x y => (P x y).toReal

omit [Fintype V] [DecidableEq V] in
/-- The entries of the kernel matrix. -/
theorem kernelMatrix_apply (P : MarkovKernel V) (x y : V) :
    kernelMatrix P x y = (P x y).toReal := rfl

omit [Fintype V] [DecidableEq V] in
/-- Every entry of the kernel matrix is non-negative. -/
theorem kernelMatrix_nonneg (P : MarkovKernel V) (x y : V) : 0 ≤ kernelMatrix P x y :=
  ENNReal.toReal_nonneg

/-- The row `q_eᵀ P^j` for the pair `e = (u, v)`: its entry `z` is
`(P^j)_uz - (P^j)_vz`. -/
def differenceRow (P : MarkovKernel V) (u v : V) (j : ℕ) (z : V) : ℝ :=
  (kernelMatrix P ^ j) u z - (kernelMatrix P ^ j) v z

omit [DecidableEq V] in
/-- Every row of the kernel matrix sums to `1`. -/
theorem kernelMatrix_row_sum (P : MarkovKernel V) (x : V) :
    ∑ z, kernelMatrix P x z = 1 :=
  (FiniteTransport.pmf_mem_simplex (P x)).2

/-- Every row of every power of the kernel matrix sums to `1`. -/
theorem kernelMatrix_pow_row_sum (P : MarkovKernel V) (j : ℕ) (x : V) :
    ∑ z, (kernelMatrix P ^ j) x z = 1 := by
  induction j with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, kernelMatrix_row_sum, mul_one]
      exact ih

/-- The entries of every row `q_eᵀ P^j` sum to `0`. -/
theorem differenceRow_row_sum (P : MarkovKernel V) (u v : V) (j : ℕ) :
    ∑ z, differenceRow P u v j z = 0 := by
  simp only [differenceRow, Finset.sum_sub_distrib, kernelMatrix_pow_row_sum, sub_self]

/-- The normalized variance `V_t(u, v) = ∑_{j<t} ‖q_eᵀ P^j‖₂²` of equation
(S22). -/
def normalizedVariance (P : MarkovKernel V) (u v : V) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, ∑ z, differenceRow P u v j z ^ 2

/-- The normalized variance `V_t(u, v)` is non-decreasing in the round `t`. -/
theorem normalizedVariance_mono (P : MarkovKernel V) (u v : V) :
    Monotone (normalizedVariance P u v) := by
  intro s t hst
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst)
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Re-indexing a sum over rounds `s ∈ (n, n + T]` by `j = n + T - s` gives a
sum over `j ∈ Finset.range T`. -/
theorem sum_Icc_shift_reindex (n T : ℕ) (F : ℕ → ℝ) :
    ∑ s ∈ Finset.Icc (n + 1) (n + T), F (n + T - s) = ∑ j ∈ Finset.range T, F j := by
  have h := Finset.sum_Ico_reflect F (n + 1) (le_refl (n + T + 1))
  rwa [Nat.sub_self, show n + T + 1 - (n + 1) = T by omega, ← Finset.range_eq_Ico,
    Finset.Ico_add_one_right_eq_Icc] at h

/-- Re-indexing a sum over rounds `s ∈ [1, t]` by `j = t - s` gives a sum
over `j ∈ Finset.range t`. -/
theorem sum_Icc_reindex (t : ℕ) (F : ℕ → ℝ) :
    ∑ s ∈ Finset.Icc 1 t, F (t - s) = ∑ j ∈ Finset.range t, F j := by
  simpa only [Nat.zero_add] using sum_Icc_shift_reindex 0 t F

/-- For distinct vertices `u` and `v`, the normalized variance after one round
is `V_1(u, v) = 2`. -/
theorem normalizedVariance_one (P : MarkovKernel V) {u v : V} (huv : u ≠ v) :
    normalizedVariance P u v 1 = 2 := by
  rw [normalizedVariance, Finset.sum_range_one]
  have h (z : V) : differenceRow P u v 0 z ^ 2 =
      (if u = z then (1 : ℝ) else 0) + (if v = z then 1 else 0) := by
    by_cases hu : u = z
    · subst z
      simp [differenceRow, huv.symm]
    · by_cases hv : v = z <;> norm_num [differenceRow, Matrix.one_apply, hu, hv]
  rw [Finset.sum_congr rfl fun z _ => h z, Finset.sum_add_distrib]
  norm_num [Finset.sum_ite_eq]

/-- `V_T(u, v) > 0` for distinct vertices and `T ≥ 1`. -/
theorem normalizedVariance_pos (P : MarkovKernel V) {u v : V} (huv : u ≠ v)
    {T : ℕ} (hT : 1 ≤ T) : 0 < normalizedVariance P u v T :=
  lt_of_lt_of_le (by norm_num)
    ((normalizedVariance_one P huv).symm.le.trans (normalizedVariance_mono P u v hT))

variable {P : MarkovKernel V} {σ : ℝ} {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (volume : Measure Ω)]

/-- Equation (S17): `f_t(x) = ∑_{j<t} ∑_z (P^j)_xz ξ_{t-j}(z)`. -/
theorem f_eq_sum_noise (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) (ω : Ω) :
    proc.f t x ω
      = ∑ j ∈ Finset.range t, ∑ z,
          (kernelMatrix P ^ j) x z * proc.ξ (t - j) z ω := by
  induction t generalizing x with
  | zero => simp [proc.f_zero]
  | succ t ih =>
      rw [proc.f_update, Finset.sum_range_succ']
      simp only [markovOperator, ← kernelMatrix_apply, ih, Finset.mul_sum, pow_zero,
        Matrix.one_apply, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq, Nat.sub_zero,
        Nat.add_sub_add_right]
      rw [Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [pow_succ', Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => (mul_assoc _ _ _).symm

/-- Equation (S17), summed over the round `s` of the noise:
`f_t(x) = ∑_{s=1}^{t} ∑_z (P^(t-s))_xz ξ_s(z)`. -/
theorem f_eq_sum_rounds (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) (ω : Ω) :
    proc.f t x ω
      = ∑ s ∈ Finset.Icc 1 t, ∑ z,
          (kernelMatrix P ^ (t - s)) x z * proc.ξ s z ω := by
  rw [f_eq_sum_noise proc t x ω,
    ← sum_Icc_reindex t (fun j => ∑ z, (kernelMatrix P ^ j) x z * proc.ξ (t - j) z ω)]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Nat.sub_sub_self (Finset.mem_Icc.mp hs).2]

/-- The edge difference as a sum over the rounds `1, …, t` of the noise:
`f_t(u) - f_t(v) = ∑_{s=1}^{t} ∑_z (q_eᵀ P^(t-s))_z ξ_s(z)`. -/
theorem edgeDiff_eq_sum_rounds (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (u v : V) (ω : Ω) :
    proc.f t u ω - proc.f t v ω =
      ∑ s ∈ Finset.Icc 1 t, ∑ z, differenceRow P u v (t - s) z * proc.ξ s z ω := by
  rw [f_eq_sum_rounds proc t u ω, f_eq_sum_rounds proc t v ω]
  simp only [differenceRow, sub_mul, Finset.sum_sub_distrib]

/-- The noise of rounds `n + 1, …, n + T`, weighted by the rows
`q_eᵀ P^(n + T - s)`, has law `N(0, σ² V_T(u, v))`. -/
theorem noiseBlock_gaussian (proc : GaussianAveragingProcess P σ Ω) (u v : V) (n T : ℕ) :
    Measure.map (fun ω => ∑ s ∈ Finset.Icc (n + 1) (n + T), ∑ z,
        differenceRow P u v (n + T - s) z * proc.ξ s z ω) volume
      = gaussianReal 0 (σ ^ 2 * normalizedVariance P u v T).toNNReal := by
  let S := Finset.Icc (n + 1) (n + T) ×ˢ (Finset.univ : Finset V)
  let c := fun p : ℕ × V => differenceRow P u v (n + T - p.1) p.2
  have h := proc.ξ_linear_combination_law S
    (fun p hp => (Nat.le_add_left 1 n).trans
      (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1) c
  simpa only [S, c, Finset.sum_product, normalizedVariance,
    sum_Icc_shift_reindex n T (fun j => ∑ z, differenceRow P u v j z ^ 2)] using h

/-- Lemma T2.1: the edge difference `D_t(u, v) = f_t(u) - f_t(v)` has law
`N(0, σ² V_t(u, v))`. -/
theorem edgeDiff_gaussian (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (u v : V) :
    Measure.map (fun ω => proc.f t u ω - proc.f t v ω) volume
      = gaussianReal 0 (σ ^ 2 * normalizedVariance P u v t).toNNReal := by
  simpa only [edgeDiff_eq_sum_rounds, Nat.zero_add] using noiseBlock_gaussian proc u v 0 t

omit [DecidableEq V] in
/-- Each value `f_t(x)` is measurable. -/
theorem measurable_f (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (x : V) :
    Measurable (proc.f t x) := by
  induction t generalizing x with
  | zero => rw [proc.f_zero]; exact measurable_const
  | succ t ih =>
      rw [funext (proc.f_succ t x)]
      exact (Finset.measurable_sum Finset.univ fun y _ => (ih y).const_mul (P x y).toReal).add
        (proc.noise_measurable t x)

end GraphStability
