import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Spectrum
import GraphStability.EffectiveCurvature
import GraphStability.VarianceLimit

/-!
# Regular graphs and the spectral gap (equation (S76))

An orthonormal eigenbasis decomposes the squared norm of each row `q_eᵀ P^j`
into a sum of geometric sequences. For a regular graph the averaging matrix is
symmetric, and the spectral theorem provides such a basis.
-/

noncomputable section

namespace GraphStability

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An orthonormal eigenbasis of the kernel matrix, with the eigenvectors as
the columns of `vectors`. -/
structure KernelEigenbasis (P : MarkovKernel V) where
  /-- The eigenvalues `λ_k`. -/
  values : V → ℝ
  /-- The matrix whose columns are the eigenvectors `φ_k`. -/
  vectors : Matrix V V ℝ
  /-- The matrix of eigenvectors is orthogonal. -/
  orthogonal : vectors * vectorsᵀ = 1
  /-- Column `k` is an eigenvector with eigenvalue `values k`. -/
  eigenvectors : kernelMatrix P * vectors = vectors * diagonal values

namespace KernelEigenbasis

variable {P : MarkovKernel V} (E : KernelEigenbasis P)

/-- The coefficient `c_k = φ_k(u) - φ_k(v)` of the pair `(u, v)` along the
`k`th eigenvector. -/
def coefficient (u v k : V) : ℝ := E.vectors u k - E.vectors v k

/-- `P^j` acts on each eigenvector `φ_k` by multiplication by `λ_k^j`. -/
theorem power_eigenvectors (j : ℕ) :
    kernelMatrix P ^ j * E.vectors = E.vectors * diagonal (fun k => E.values k ^ j) := by
  have h : SemiconjBy E.vectors (diagonal E.values) (kernelMatrix P) := E.eigenvectors.symm
  simpa only [diagonal_pow] using Eq.symm (h.pow_right j)

/-- Coordinate `k` of `differenceRow P u v j` in the eigenbasis `E` is `c_k λ_k^j`. -/
theorem differenceRow_coordinates (u v : V) (j : ℕ) (k : V) :
    (differenceRow P u v j ᵥ* E.vectors) k = E.coefficient u v k * E.values k ^ j := by
  change (∑ z, ((kernelMatrix P ^ j) u z - (kernelMatrix P ^ j) v z) * E.vectors z k) = _
  simp only [sub_mul, sum_sub_distrib, ← Matrix.mul_apply, E.power_eigenvectors,
    Matrix.mul_diagonal, coefficient]

/-- Parseval's identity for row vectors in the orthonormal eigenbasis `E`. -/
theorem parseval (w : V → ℝ) :
    ∑ z, w z ^ 2 = ∑ k, (w ᵥ* E.vectors) k ^ 2 := by
  have hdot : (w ᵥ* E.vectors) ⬝ᵥ (w ᵥ* E.vectors) = w ⬝ᵥ w := by
    rw [← dotProduct_mulVec, mulVec_vecMul, E.orthogonal, one_mulVec]
  simpa only [dotProduct, pow_two] using hdot.symm

/-- The squared Euclidean norm of `differenceRow P u v j` equals `∑_k c_k² (λ_k²)^j`. -/
theorem differenceRow_sqNorm (u v : V) (j : ℕ) :
    (∑ z, differenceRow P u v j z ^ 2) =
      ∑ k, E.coefficient u v k ^ 2 * (E.values k ^ 2) ^ j := by
  rw [E.parseval (differenceRow P u v j)]
  exact sum_congr rfl fun k _ => by
    rw [E.differenceRow_coordinates, mul_pow, pow_right_comm (E.values k) j 2]

/-- For distinct vertices `u` and `v`, `∑_k c_k² = 2`. -/
theorem coefficient_sq_sum {u v : V} (huv : u ≠ v) :
    ∑ k, E.coefficient u v k ^ 2 = 2 := by
  simpa only [normalizedVariance, Finset.sum_range_one, E.differenceRow_sqNorm, pow_zero,
    mul_one] using normalizedVariance_one P huv

/-- If the series defining `V_∞(u, v)` converges, so does `∑_j c_k² (λ_k²)^j` for each `k`. -/
theorem spectral_term_summable (u v k : V)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) :
    Summable (fun j : ℕ => E.coefficient u v k ^ 2 * (E.values k ^ 2) ^ j) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (sq_nonneg _) (pow_nonneg (sq_nonneg _) _)) _ hs
  intro j
  rw [E.differenceRow_sqNorm]
  exact single_le_sum (fun l _ => mul_nonneg (sq_nonneg (E.coefficient u v l))
    (pow_nonneg (sq_nonneg (E.values l)) j))
    (mem_univ k)

/-- If the series defining `V_∞(u, v)` converges, every eigenvector on which
the pair has a non-zero coefficient has eigenvalue of absolute value less than
one. -/
theorem eigenvalue_sq_lt_one_of_coefficient_ne_zero (u v k : V)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2))
    (hc : E.coefficient u v k ≠ 0) : E.values k ^ 2 < 1 := by
  have hg : Summable (fun j : ℕ => (E.values k ^ 2) ^ j) :=
    (summable_mul_left_iff (pow_ne_zero 2 hc)).mp (E.spectral_term_summable u v k hs)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E.values k))] using
    summable_geometric_iff_norm_lt_one.mp hg

/-- If the series defining `V_∞(u, v)` converges, then
`V_∞(u, v) = ∑_k c_k² / (1 - λ_k²)`; the terms with `c_k = 0` vanish. -/
theorem limitingVariance_eq_sum (u v : V)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) :
    limitingVariance P u v = ∑ k, E.coefficient u v k ^ 2 / (1 - E.values k ^ 2) := by
  unfold limitingVariance
  simp_rw [E.differenceRow_sqNorm]
  rw [Summable.tsum_finsetSum (fun k _ => E.spectral_term_summable u v k hs)]
  apply sum_congr rfl
  intro k _
  by_cases hc : E.coefficient u v k = 0
  · simp [hc]
  · have hlt := E.eigenvalue_sq_lt_one_of_coefficient_ne_zero u v k hs hc
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hlt, div_eq_mul_inv]

/-- For distinct `u`, `v`, if the series defining `V_∞(u, v)` converges and
`|λ_k| ≤ r` with `0 ≤ r < 1` for every eigenvector with non-zero coefficient
`c_k`, then `V_∞(u, v) ≤ 2 / (1 - r²)`. -/
theorem limitingVariance_le_of_eigenvalue_bound {u v : V} (huv : u ≠ v)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ k, E.coefficient u v k ≠ 0 → |E.values k| ≤ r) :
    limitingVariance P u v ≤ 2 / (1 - r ^ 2) := by
  have hrden : 0 < 1 - r ^ 2 := sub_pos.mpr ((sq_lt_one_iff₀ hr0).2 hr1)
  rw [E.limitingVariance_eq_sum u v hs]
  calc
    (∑ k, E.coefficient u v k ^ 2 / (1 - E.values k ^ 2))
        ≤ ∑ k, E.coefficient u v k ^ 2 / (1 - r ^ 2) := by
      apply sum_le_sum
      intro k _
      by_cases hc : E.coefficient u v k = 0
      · simp [hc]
      · apply div_le_div_of_nonneg_left (sq_nonneg _) hrden
        exact sub_le_sub_left (sq_le_sq.mpr (by
          simpa only [abs_of_nonneg hr0] using hbound k hc)) 1
    _ = 2 / (1 - r ^ 2) := by rw [← sum_div, E.coefficient_sq_sum huv]

/-- The largest eigenvalue below `1`, and `0` if there is none. For the
averaging rule of a connected regular graph with at least two vertices it is
the second eigenvalue `λ₂`
(`regular_largestEigenvalueBelowOne_attained`, `regular_eigenvector_one_constant`). -/
def largestEigenvalueBelowOne : ℝ :=
  if h : (univ.filter fun k => E.values k < 1).Nonempty then
    (univ.filter fun k => E.values k < 1).sup' h E.values
  else 0

/-- Every eigenvalue strictly below `1` is at most `largestEigenvalueBelowOne`. -/
theorem le_largestEigenvalueBelowOne (k : V) (hk : E.values k < 1) :
    E.values k ≤ E.largestEigenvalueBelowOne := by
  have hmem : k ∈ univ.filter (fun k => E.values k < 1) :=
    mem_filter.mpr ⟨mem_univ _, hk⟩
  rw [largestEigenvalueBelowOne, dif_pos ⟨k, hmem⟩]
  exact le_sup' E.values hmem

end KernelEigenbasis

/-- An orthonormal eigenbasis of a symmetric kernel, from the spectral theorem. -/
def kernelEigenbasis (P : MarkovKernel V) (hP : (kernelMatrix P).IsHermitian) :
    KernelEigenbasis P where
  values := hP.eigenvalues
  vectors := hP.eigenvectorUnitary
  orthogonal := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_mul_star_self hP.eigenvectorUnitary
  eigenvectors := by
    have h := congrArg (fun A : Matrix V V ℝ => A * hP.eigenvectorUnitary) hP.spectral_theorem
    simpa only [mul_assoc, unitary.coe_star_mul_self, mul_one] using h

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (hd : ∀ x : V, 0 < G.degree x)
  {d₀ : ℕ} (hreg : G.IsRegularOfDegree d₀)

include hreg

/-- On a regular graph, the averaging matrix is symmetric. -/
theorem regular_lazyKernel_isHermitian : (kernelMatrix (lazyKernel G hd)).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext x y
  simp only [Matrix.transpose_apply, kernelMatrix_apply, lazyKernel_toReal, lazyMass,
    hreg x, hreg y, eq_comm, G.adj_comm]

/-- An orthonormal eigenbasis of the averaging rule of a regular graph, from
the spectral theorem for real symmetric matrices. -/
def regularEigenbasis : KernelEigenbasis (lazyKernel G hd) :=
  kernelEigenbasis _ (regular_lazyKernel_isHermitian G hd hreg)

/-- Every eigenvalue of the averaging rule of a regular graph lies in
`[0, 1]`. -/
theorem regular_eigenvalues_range (k : V) :
    0 ≤ (regularEigenbasis G hd hreg).values k ∧
      (regularEigenbasis G hd hreg).values k ≤ 1 := by
  let A := kernelMatrix (lazyKernel G hd)
  have hA := regular_lazyKernel_isHermitian G hd hreg
  have heigen : Module.End.HasEigenvalue A.toLin' (hA.eigenvalues k) := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact hA.eigenvalues_mem_spectrum_real k
  obtain ⟨x, hx⟩ := eigenvalue_mem_ball heigen
  have hdiag : A x x = (1 : ℝ) / 2 := by
    simp [A, kernelMatrix_apply, lazyKernel_toReal, lazyMass]
  have hradius : (∑ y ∈ univ.erase x, ‖A x y‖) = 1 - A x x := by
    calc
      _ = ∑ y ∈ univ.erase x, A x y :=
        sum_congr rfl fun y _ => Real.norm_of_nonneg (kernelMatrix_nonneg (lazyKernel G hd) x y)
      _ = _ := by
        rw [sum_erase_eq_sub (mem_univ x), show ∑ y, A x y = 1 from kernelMatrix_row_sum _ x]
  rw [hradius, hdiag, Real.closedBall_eq_Icc] at hx
  norm_num [Set.mem_Icc] at hx
  exact hx

variable (hG : G.Connected)

include hG

/-- On a connected regular graph, an eigenvector on which the pair `(u, v)` has
a non-zero coefficient has eigenvalue below `1`. -/
private theorem regular_eigenvalue_lt_one_of_coefficient_ne_zero (u v k : V)
    (hc : (regularEigenbasis G hd hreg).coefficient u v k ≠ 0) :
    (regularEigenbasis G hd hreg).values k < 1 := by
  have hsq := (regularEigenbasis G hd hreg).eigenvalue_sq_lt_one_of_coefficient_ne_zero u v k
    (lazyKernel_variance_summable G hd hG u v) hc
  exact (abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq)).2

/-- On a connected regular graph, every eigenvector of the basis with
eigenvalue `1` is constant. -/
theorem regular_eigenvector_one_constant (k : V)
    (hk : (regularEigenbasis G hd hreg).values k = 1) (u v : V) :
    (regularEigenbasis G hd hreg).vectors u k = (regularEigenbasis G hd hreg).vectors v k := by
  by_contra hne
  exact (regular_eigenvalue_lt_one_of_coefficient_ne_zero G hd hreg hG u v k
    (sub_ne_zero.mpr hne)).ne hk

/-- Equation (S76): on a connected regular graph,
`V_∞(u, v) = ∑_{λ_k < 1} c_k² / (1 - λ_k²)` for all vertices `u`, `v`. -/
theorem regular_spectral_variance (u v : V) :
    limitingVariance (lazyKernel G hd) u v =
      ∑ k ∈ univ.filter (fun k => (regularEigenbasis G hd hreg).values k < 1),
        (regularEigenbasis G hd hreg).coefficient u v k ^ 2 /
          (1 - (regularEigenbasis G hd hreg).values k ^ 2) := by
  rw [(regularEigenbasis G hd hreg).limitingVariance_eq_sum u v
    (lazyKernel_variance_summable G hd hG u v)]
  symm
  refine sum_filter_of_ne fun k _ hk => ?_
  exact regular_eigenvalue_lt_one_of_coefficient_ne_zero G hd hreg hG u v k
    (fun hc => hk (by simp [hc]))

/-- On a connected regular graph, some eigenvalue below `1` attains the maximum
over those eigenvalues. -/
theorem regular_largestEigenvalueBelowOne_attained :
    let E := regularEigenbasis G hd hreg
    ∃ k, E.values k < 1 ∧ E.values k = E.largestEigenvalueBelowOne := by
  intro E
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp (hd u)
  obtain ⟨k, _, hk⟩ :=
    exists_ne_zero_of_sum_ne_zero ((E.coefficient_sq_sum huv.ne).trans_ne two_ne_zero)
  have h : (univ.filter fun j => E.values j < 1).Nonempty :=
    ⟨k, mem_filter.mpr ⟨mem_univ _,
      regular_eigenvalue_lt_one_of_coefficient_ne_zero G hd hreg hG u v k
        ((pow_ne_zero_iff two_ne_zero).mp hk)⟩⟩
  obtain ⟨j, hj, heq⟩ := exists_mem_eq_sup' h E.values
  refine ⟨j, (mem_filter.mp hj).2, ?_⟩
  simpa only [KernelEigenbasis.largestEigenvalueBelowOne, dif_pos h] using heq.symm

/-- On a connected regular graph, the largest eigenvalue below one lies in
`[0, 1)`. -/
private theorem regular_largestEigenvalueBelowOne_range :
    (regularEigenbasis G hd hreg).largestEigenvalueBelowOne ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨k, hk, heq⟩ := regular_largestEigenvalueBelowOne_attained G hd hreg hG
  rw [← heq]
  exact ⟨(regular_eigenvalues_range G hd hreg k).1, hk⟩

/-- Equation (S76): on a connected regular graph, `V_∞(u, v) ≤ 2 / (1 - λ₂²)`
for distinct vertices `u` and `v`, where `λ₂` is the largest eigenvalue below
`1`. -/
theorem regular_spectral_variance_bound {u v : V} (huv : u ≠ v) :
    limitingVariance (lazyKernel G hd) u v ≤
      2 / (1 - (regularEigenbasis G hd hreg).largestEigenvalueBelowOne ^ 2) := by
  let E := regularEigenbasis G hd hreg
  have hr := regular_largestEigenvalueBelowOne_range G hd hreg hG
  apply E.limitingVariance_le_of_eigenvalue_bound huv (lazyKernel_variance_summable G hd hG u v)
    hr.1 hr.2
  intro k hc
  rw [abs_of_nonneg (regular_eigenvalues_range G hd hreg k).1]
  apply E.le_largestEigenvalueBelowOne k
  exact regular_eigenvalue_lt_one_of_coefficient_ne_zero G hd hreg hG u v k hc

/-- Equation (S76): on a connected regular graph, `κ_eff(u, v) ≥ 1 - λ₂` for
distinct vertices `u`, `v`. -/
theorem regular_effectiveCurvature_ge_spectralGap {u v : V} (huv : u ≠ v) :
    1 - (regularEigenbasis G hd hreg).largestEigenvalueBelowOne ≤
      effectiveCurvature (limitingVariance (lazyKernel G hd) u v) := by
  have h2 := limitingVariance_ge_two _ huv (lazyKernel_variance_summable G hd hG u v)
  have hle := regular_spectral_variance_bound G hd hreg hG huv
  have h := effectiveCurvature_antitoneOn h2 (h2.trans hle) hle
  rwa [effectiveCurvature_equivalentBond
    (regular_largestEigenvalueBelowOne_range G hd hreg hG).1] at h

end GraphStability
