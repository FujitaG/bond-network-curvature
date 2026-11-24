import GraphStability.VarianceLimit

/-!
# The covariance equation (Proposition T2.6)
-/

noncomputable section

namespace GraphStability

open Finset Filter Matrix
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The matrix `(1/n) 𝟙𝟙ᵀ`, which replaces every vertex value by the average
over all vertices. -/
def meanMatrix : Matrix V V ℝ := fun _ _ => (Fintype.card V : ℝ)⁻¹

/-- The centring matrix `H = I - (1/n) 𝟙𝟙ᵀ`. -/
def centeringMatrix : Matrix V V ℝ := 1 - meanMatrix

/-- The centred kernel matrix `B = HP`; it equals `HPH`
(`centeredKernel_mul_centering`). -/
def centeredKernel (P : MarkovKernel V) : Matrix V V ℝ := centeringMatrix * kernelMatrix P

/-- The matrix `H P^j`, which carries the noise added `j` rounds earlier into
the centred values. -/
def centeredPower (P : MarkovKernel V) (j : ℕ) : Matrix V V ℝ :=
  centeringMatrix * kernelMatrix P ^ j

/-- The term `(HP^j)(HP^j)ᵀ` of the normalized covariance: the contribution of
the noise added `j` rounds earlier. -/
def covarianceTerm (P : MarkovKernel V) (j : ℕ) : Matrix V V ℝ :=
  centeredPower P j * (centeredPower P j)ᵀ

/-- The normalized covariance `S_t = ∑_{j<t} (HP^j)(HP^j)ᵀ` after `t` rounds. -/
def normalizedCovariance (P : MarkovKernel V) (t : ℕ) : Matrix V V ℝ :=
  ∑ j ∈ range t, covarianceTerm P j

/-- The sum `S = ∑_j (HP^j)(HP^j)ᵀ`. When the series converges, `S` is the
limit of `S_t` (`normalizedCovariance_tendsto`) and solves the covariance
equation (`covarianceEquation_limitingCovariance`). -/
def limitingCovariance (P : MarkovKernel V) : Matrix V V ℝ := ∑' j, covarianceTerm P j

omit [DecidableEq V] in
/-- Every row of `meanMatrix` sums to `1`. -/
theorem meanMatrix_row_sum (x : V) : ∑ y, (meanMatrix : Matrix V V ℝ) x y = 1 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨x⟩).ne'
  simp [meanMatrix, hn]

/-- Every row of `centeringMatrix` sums to `0`. -/
theorem centeringMatrix_row_sum (x : V) :
    ∑ y, (centeringMatrix : Matrix V V ℝ) x y = 0 := by
  simp only [centeringMatrix, Matrix.sub_apply, sum_sub_distrib, meanMatrix_row_sum]
  simp [Matrix.one_apply]

omit [DecidableEq V] in
/-- Left multiplication by a matrix whose rows sum to one fixes the mean matrix. -/
theorem mul_meanMatrix_of_row_sum (A : Matrix V V ℝ) (hA : ∀ x, ∑ z, A x z = 1) :
    A * meanMatrix = meanMatrix := by
  ext x y
  simp only [Matrix.mul_apply, meanMatrix, ← sum_mul, hA, one_mul]

/-- `centeringMatrix` is symmetric. -/
theorem centeringMatrix_transpose : (centeringMatrix : Matrix V V ℝ)ᵀ = centeringMatrix := by
  ext x y
  simp [centeringMatrix, meanMatrix, Matrix.one_apply, eq_comm]

/-- `B H = B`. -/
theorem centeredKernel_mul_centering (P : MarkovKernel V) :
    centeredKernel P * centeringMatrix = centeredKernel P := by
  unfold centeredKernel
  nth_rw 2 [centeringMatrix]
  rw [mul_sub, mul_one, mul_assoc, mul_meanMatrix_of_row_sum _ (kernelMatrix_row_sum P)]
  have hzero : (centeringMatrix : Matrix V V ℝ) * meanMatrix = 0 :=
    IsIdempotentElem.one_sub_mul_self
      (mul_meanMatrix_of_row_sum (meanMatrix : Matrix V V ℝ) meanMatrix_row_sum)
  rw [hzero, sub_zero]

/-- `centeredPower P (j + 1) = B * centeredPower P j`. -/
theorem centeredPower_succ (P : MarkovKernel V) (j : ℕ) :
    centeredPower P (j + 1) = centeredKernel P * centeredPower P j := by
  unfold centeredPower
  rw [← mul_assoc, centeredKernel_mul_centering, centeredKernel, mul_assoc, ← pow_succ']

/-- The `j = 0` covariance term is `H`. -/
theorem covarianceTerm_zero (P : MarkovKernel V) :
    covarianceTerm P 0 = centeringMatrix := by
  rw [covarianceTerm, centeredPower, pow_zero, mul_one, centeringMatrix_transpose]
  exact (IsIdempotentElem.one_sub
    (mul_meanMatrix_of_row_sum (meanMatrix : Matrix V V ℝ) meanMatrix_row_sum)).eq

/-- `covarianceTerm P (j + 1) = B * covarianceTerm P j * Bᵀ`. -/
theorem covarianceTerm_succ (P : MarkovKernel V) (j : ℕ) :
    covarianceTerm P (j + 1) = centeredKernel P * covarianceTerm P j * (centeredKernel P)ᵀ := by
  rw [covarianceTerm, centeredPower_succ, Matrix.transpose_mul, covarianceTerm]
  simp only [mul_assoc]

/-- The recursion `S_{t+1} = B S_t Bᵀ + H`. -/
theorem normalizedCovariance_succ (P : MarkovKernel V) (t : ℕ) :
    normalizedCovariance P (t + 1) =
      centeredKernel P * normalizedCovariance P t * (centeredKernel P)ᵀ + centeringMatrix := by
  simp only [normalizedCovariance, sum_range_succ', covarianceTerm_succ, covarianceTerm_zero,
    mul_sum, sum_mul]

/-- If some positive power of `P` has positive entries, the `rowL1` norms of row `x` of
`HP^j` are summable over `j`. -/
theorem centeredPower_row_summable (P : MarkovKernel V) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hpos : ∀ x y, 0 < (kernelMatrix P ^ ℓ) x y) (x : V) :
    Summable (fun j : ℕ => rowL1 (centeredPower P j x)) :=
  haveI : Nonempty V := ⟨x⟩
  rowL1_summable_of_positive_power P ℓ hℓ hpos _ (centeringMatrix_row_sum x)

/-- If some positive power of `P` has positive entries, the covariance terms are summable. -/
theorem covarianceTerm_summable (P : MarkovKernel V) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hpos : ∀ x y, 0 < (kernelMatrix P ^ ℓ) x y) : Summable (covarianceTerm P) := by
  refine Pi.summable.mpr fun x => Pi.summable.mpr fun y => ?_
  exact row_dotProduct_summable P (centeringMatrix x) (centeringMatrix y)
    (centeredPower_row_summable P ℓ hℓ hpos x)

/-- When the covariance series converges, `S_t` tends to `limitingCovariance P`. -/
theorem normalizedCovariance_tendsto (P : MarkovKernel V)
    (hs : Summable (covarianceTerm P)) :
    Tendsto (normalizedCovariance P) atTop (𝓝 (limitingCovariance P)) :=
  hs.hasSum.tendsto_sum_nat

/-- When the covariance series converges, its sum `S` satisfies the covariance
equation `S - B S Bᵀ = H`. -/
theorem covarianceEquation_limitingCovariance (P : MarkovKernel V)
    (hs : Summable (covarianceTerm P)) :
    limitingCovariance P -
      centeredKernel P * limitingCovariance P * (centeredKernel P)ᵀ = centeringMatrix := by
  have hshift : (∑' j : ℕ, covarianceTerm P (j + 1)) =
      centeredKernel P * limitingCovariance P * (centeredKernel P)ᵀ := by
    simp_rw [covarianceTerm_succ]
    rw [(hs.mul_left _).tsum_mul_right, hs.tsum_mul_left]
    rfl
  have heq := hs.tsum_eq_zero_add
  rw [covarianceTerm_zero, hshift] at heq
  exact sub_eq_iff_eq_add.mpr heq

/-- `B^(j + 1) = H P^(j + 1)`. -/
theorem centeredKernel_pow_succ (P : MarkovKernel V) (j : ℕ) :
    centeredKernel P ^ (j + 1) = centeredPower P (j + 1) := by
  induction j with
  | zero => simp [centeredKernel, centeredPower]
  | succ j ih => rw [pow_succ', ih, ← centeredPower_succ]

/-- If some positive power of `P` has positive entries, `B^j → 0` as `j → ∞`. -/
theorem centeredKernel_pow_tendsto_zero (P : MarkovKernel V) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hpos : ∀ x y, 0 < (kernelMatrix P ^ ℓ) x y) :
    Tendsto (fun j : ℕ => centeredKernel P ^ j) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simp_rw [centeredKernel_pow_succ]
  refine tendsto_pi_nhds.mpr fun x => tendsto_pi_nhds.mpr fun y => ?_
  exact squeeze_zero_norm (fun j => abs_le_rowL1 (centeredPower P (j + 1) x) y)
    ((centeredPower_row_summable P ℓ hℓ hpos x).tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1))

/-- If some positive power of `P` has positive entries, the covariance equation
`S - B S Bᵀ = H` has at most one solution. -/
theorem covarianceEquation_unique (P : MarkovKernel V) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hpos : ∀ x y, 0 < (kernelMatrix P ^ ℓ) x y)
    (S S' : Matrix V V ℝ)
    (hS : S - centeredKernel P * S * (centeredKernel P)ᵀ = centeringMatrix)
    (hS' : S' - centeredKernel P * S' * (centeredKernel P)ᵀ = centeringMatrix) : S = S' := by
  let B := centeredKernel P
  let C := S - S'
  have hC : C = B * C * Bᵀ := by
    change S - S' = B * (S - S') * Bᵀ
    rw [mul_sub, sub_mul]
    exact sub_eq_sub_iff_sub_eq_sub.mp (hS.trans hS'.symm)
  have hiter (j : ℕ) : C = B ^ j * C * (B ^ j)ᵀ := by
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          C = B * C * Bᵀ := hC
          _ = B * (B ^ j * C * (B ^ j)ᵀ) * Bᵀ := congrArg (fun X => B * X * Bᵀ) ih
          _ = B ^ (j + 1) * C * (B ^ (j + 1))ᵀ := by
            rw [pow_succ', Matrix.transpose_mul]
            simp only [mul_assoc]
  have hB := centeredKernel_pow_tendsto_zero P ℓ hℓ hpos
  have hBt : Tendsto (fun j : ℕ => (B ^ j)ᵀ) atTop (𝓝 0) :=
    (continuous_id.matrix_transpose.tendsto 0).comp hB
  have hlim : Tendsto (fun j : ℕ => B ^ j * C * (B ^ j)ᵀ) atTop (𝓝 0) := by
    simpa using (hB.mul tendsto_const_nhds).mul hBt
  have hzero : C = 0 := tendsto_nhds_unique tendsto_const_nhds (by
    simpa only [← hiter] using hlim)
  exact sub_eq_zero.mp hzero

/-- The difference of rows `u` and `v` of `H P^j` is the row `q_eᵀ P^j`. -/
theorem centeredPower_differenceRow (P : MarkovKernel V) (j : ℕ) (u v z : V) :
    centeredPower P j u z - centeredPower P j v z = differenceRow P u v j z := by
  unfold centeredPower centeringMatrix differenceRow
  rw [sub_mul, one_mul]
  exact sub_sub_sub_cancel_right _ _ _

/-- For `C = covarianceTerm P j`, `C_uu + C_vv - 2 C_uv = ‖q_eᵀ P^j‖₂²`. -/
theorem covarianceTerm_differenceRow (P : MarkovKernel V) (j : ℕ) (u v : V) :
    covarianceTerm P j u u + covarianceTerm P j v v - 2 * covarianceTerm P j u v =
      ∑ z, differenceRow P u v j z ^ 2 := by
  simp only [covarianceTerm, Matrix.mul_apply, Matrix.transpose_apply, ← sum_add_distrib,
    mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro z _
  rw [← centeredPower_differenceRow P j u v z]
  ring

/-- If the covariance series converges, then
`V_∞(u, v) = S_uu + S_vv - 2 S_uv` with `S = limitingCovariance P`. -/
theorem limitingVariance_eq_covariance (P : MarkovKernel V) (u v : V)
    (hs : Summable (covarianceTerm P)) :
    limitingVariance P u v = limitingCovariance P u u + limitingCovariance P v v -
      2 * limitingCovariance P u v := by
  have hentry (x y : V) :
      HasSum (fun j => covarianceTerm P j x y) (limitingCovariance P x y) :=
    Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum x) y
  have h := ((hentry u u).add (hentry v v)).sub ((hentry u v).mul_left 2)
  simp only [covarianceTerm_differenceRow] at h
  exact h.tsum_eq

open MeasureTheory ProbabilityTheory

variable {P : MarkovKernel V} {σ : ℝ} {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (volume : Measure Ω)]

/-- The centred values `f̃_t = H f_t`: the vertex values minus their average
over the vertices. -/
def centeredValues (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) (ω : Ω) : ℝ :=
  ∑ y, centeringMatrix x y * proc.f t y ω

/-- Centring leaves all pair differences unchanged. -/
theorem centeredValues_difference (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (u v : V) (ω : Ω) :
    centeredValues proc t u ω - centeredValues proc t v ω = proc.f t u ω - proc.f t v ω := by
  change (centeringMatrix *ᵥ (fun x => proc.f t x ω)) u -
    (centeringMatrix *ᵥ (fun x => proc.f t x ω)) v = _
  rw [centeringMatrix, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_sub_sub_cancel_right _ _ _

/-- Equation (S69): the centred values satisfy `f̃_{t+1} = B f̃_t + H ξ_{t+1}`. -/
theorem centeredValues_update (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (ω : Ω) :
    (fun x => centeredValues proc (t + 1) x ω) =
      centeredKernel P *ᵥ (fun x => centeredValues proc t x ω) +
        centeringMatrix *ᵥ (fun x => proc.ξ (t + 1) x ω) := by
  have hup : (fun x => proc.f (t + 1) x ω) =
      kernelMatrix P *ᵥ (fun x => proc.f t x ω) + (fun x => proc.ξ (t + 1) x ω) :=
    funext (fun x => proc.f_update t x ω)
  change centeringMatrix *ᵥ (fun x => proc.f (t + 1) x ω) =
    centeredKernel P *ᵥ (centeringMatrix *ᵥ (fun x => proc.f t x ω)) + _
  rw [hup, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    centeredKernel_mul_centering]
  rfl

/-- Distinct noise coordinates are uncorrelated, and each has variance `σ²`. -/
theorem noise_covariance (proc : GaussianAveragingProcess P σ Ω) (p q : ℕ × V) :
    cov[proc.noise p.1 p.2, proc.noise q.1 q.2] = if p = q then σ ^ 2 else 0 := by
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl, covariance_self (proc.noise_measurable p.1 p.2).aemeasurable,
      (proc.noise_identDistrib p.1 p.2).variance_eq, variance_id_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg σ)]
  · rw [if_neg hpq]
    exact (proc.noise_indep.indepFun hpq).covariance_eq_zero
      (proc.noise_memLp_two p) (proc.noise_memLp_two q)

/-- The covariance of two finite linear combinations `∑ a_p noise_p` and
`∑ b_p noise_p` of the noise is `σ² ∑ a_p b_p`. -/
theorem covariance_weighted_noise_sum (proc : GaussianAveragingProcess P σ Ω)
    (S : Finset (ℕ × V)) (a b : ℕ × V → ℝ) :
    cov[(fun ω => ∑ p ∈ S, a p * proc.noise p.1 p.2 ω),
      (fun ω => ∑ p ∈ S, b p * proc.noise p.1 p.2 ω)] =
        σ ^ 2 * ∑ p ∈ S, a p * b p := by
  rw [covariance_fun_sum_fun_sum'
    (fun p _ => (proc.noise_memLp_two p).const_mul (a p))
    (fun p _ => (proc.noise_memLp_two p).const_mul (b p))]
  simp_rw [covariance_mul_left, covariance_mul_right, noise_covariance]
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  simp only [mul_ite, mul_zero, sum_ite_eq, hp, if_true]
  ring

/-- The covariance of `∑ a_p ξ_p` and `∑ b_p ξ_p`, over rounds `t ≥ 1`, is
`σ² ∑ a_p b_p`. -/
theorem covariance_weighted_ξ_sum (proc : GaussianAveragingProcess P σ Ω)
    (S : Finset (ℕ × V)) (hS : ∀ p ∈ S, 1 ≤ p.1) (a b : ℕ × V → ℝ) :
    cov[(fun ω => ∑ p ∈ S, a p * proc.ξ p.1 p.2 ω),
      (fun ω => ∑ p ∈ S, b p * proc.ξ p.1 p.2 ω)] =
        σ ^ 2 * ∑ p ∈ S, a p * b p := by
  have hfun : ∀ c : ℕ × V → ℝ, (fun ω => ∑ p ∈ S, c p * proc.ξ p.1 p.2 ω)
      = fun ω => ∑ q ∈ S.image (fun p : ℕ × V => (p.1 - 1, p.2)),
          c (q.1 + 1, q.2) * proc.noise q.1 q.2 ω := fun c => by
    funext ω
    exact (sum_image_pred_fst S hS (fun p => c p * proc.ξ p.1 p.2 ω)).symm
  rw [hfun a, hfun b, covariance_weighted_noise_sum,
    sum_image_pred_fst S hS (fun p => a p * b p)]

/-- The centred values are the sum of the past noise weighted by the matrices
`H P^(t-s)`. -/
theorem centeredValues_eq_noise_sum (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (x : V) :
    centeredValues proc t x = fun ω =>
      ∑ p ∈ Icc 1 t ×ˢ (univ : Finset V),
        centeredPower P (t - p.1) x p.2 * proc.ξ p.1 p.2 ω := by
  funext ω
  simp only [centeredValues, sum_product]
  simp_rw [f_eq_sum_rounds proc t, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp only [centeredPower, Matrix.mul_apply, sum_mul, mul_assoc]

/-- The covariance of the centred values at `x` and `y` is `σ²` times the
entry `(x, y)` of `normalizedCovariance`. -/
theorem centeredValues_covariance (proc : GaussianAveragingProcess P σ Ω)
    (t : ℕ) (x y : V) :
    cov[centeredValues proc t x, centeredValues proc t y] =
      σ ^ 2 * normalizedCovariance P t x y := by
  rw [centeredValues_eq_noise_sum proc t x, centeredValues_eq_noise_sum proc t y,
    covariance_weighted_ξ_sum proc _ (fun p hp => (mem_Icc.mp (mem_product.mp hp).1).1),
    sum_product]
  congr 1
  change (∑ s ∈ Icc 1 t, ∑ z,
      centeredPower P (t - s) x z * centeredPower P (t - s) y z) = _
  rw [sum_Icc_reindex t (fun j => ∑ z, centeredPower P j x z * centeredPower P j y z)]
  simp only [normalizedCovariance, covarianceTerm, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Each centred value `centeredValues proc t x` has expectation `0`. -/
theorem centeredValues_integral_zero (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) :
    ∫ ω, centeredValues proc t x ω = 0 := by
  rw [centeredValues_eq_noise_sum, integral_finset_sum]
  · simp only [integral_const_mul, GaussianAveragingProcess.ξ_integral_zero, mul_zero,
      sum_const_zero]
  · intro p _
    exact ((proc.noise_memLp_two (p.1 - 1, p.2)).integrable (by norm_num)).const_mul _

/-- For `σ ≠ 0`, `𝔼[f̃_t(x) f̃_t(y)] / σ²` is entry `(x, y)` of
`normalizedCovariance P t`. -/
theorem centeredValues_normalized_second_moment (proc : GaussianAveragingProcess P σ Ω)
    (hσ : σ ≠ 0) (t : ℕ) (x y : V) :
    (∫ ω, centeredValues proc t x ω * centeredValues proc t y ω) / σ ^ 2 =
      normalizedCovariance P t x y := by
  have h := centeredValues_covariance proc t x y
  simp only [covariance, centeredValues_integral_zero, sub_zero] at h
  rwa [div_eq_iff (pow_ne_zero 2 hσ), mul_comm]

end GraphStability
