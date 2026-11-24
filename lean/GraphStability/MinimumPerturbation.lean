import GraphStability.Variance

/-!
# Squared perturbations needed to reach the threshold (Lemma T2.2)

For a fixed round `T`, the Cauchy–Schwarz inequality bounds the edge difference
produced by perturbations over rounds `1, …, T`, and perturbations
proportional to the rows `q_eᵀ P^(T-s)` attain the bound.
-/

namespace GraphStability

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The squared coefficients of the perturbations of rounds `1, …, T` sum to
`V_T(u, v)`. -/
private theorem perturbation_coefficient_sq_sum (P : MarkovKernel V) (u v : V) (T : ℕ) :
    (∑ s ∈ Icc 1 T, ∑ z, differenceRow P u v (T - s) z ^ 2) =
      normalizedVariance P u v T :=
  sum_Icc_reindex T (fun j => ∑ z, differenceRow P u v j z ^ 2)

/-- By the Cauchy–Schwarz inequality over rounds `1, …, T` and vertices, the
squared edge difference is at most `V_T(u, v)` times the sum of squared
perturbations. -/
theorem perturbation_response_sq_le (P : MarkovKernel V) (u v : V) (T : ℕ)
    (ζ : ℕ → V → ℝ) :
    (∑ s ∈ Icc 1 T, ∑ z, differenceRow P u v (T - s) z * ζ s z) ^ 2 ≤
      normalizedVariance P u v T * (∑ s ∈ Icc 1 T, ∑ z, ζ s z ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 T ×ˢ (univ : Finset V))
    (fun p => differenceRow P u v (T - p.1) p.2) (fun p => ζ p.1 p.2)
  simpa only [sum_product, perturbation_coefficient_sq_sum] using h

/-- When `V_T(u, v) > 0`, the perturbations
`ζ_s(z) = (θ / V_T(u, v)) (q_eᵀ P^(T-s))_z` produce edge difference `θ` and
have sum of squares `θ² / V_T(u, v)`. -/
theorem aligned_perturbation_attains (P : MarkovKernel V) {u v : V} {T : ℕ}
    (hV : 0 < normalizedVariance P u v T) (θ : ℝ) :
    (∑ s ∈ Icc 1 T, ∑ z, differenceRow P u v (T - s) z *
      (θ / normalizedVariance P u v T * differenceRow P u v (T - s) z)) = θ ∧
    (∑ s ∈ Icc 1 T, ∑ z,
      (θ / normalizedVariance P u v T * differenceRow P u v (T - s) z) ^ 2) =
      θ ^ 2 / normalizedVariance P u v T := by
  constructor
  · simp_rw [show ∀ a : ℝ, a * (θ / normalizedVariance P u v T * a) =
        θ / normalizedVariance P u v T * a ^ 2 by intro a; ring,
      ← mul_sum]
    rw [perturbation_coefficient_sq_sum]
    exact div_mul_cancel₀ θ hV.ne'
  · simp_rw [mul_pow, ← mul_sum]
    rw [perturbation_coefficient_sq_sum]
    field_simp

/-- Lemma T2.2: for distinct vertices `u`, `v` and `T ≥ 1`, the minimum sum of
squared perturbations over rounds `1, …, T` for which the edge difference has
absolute value at least `θ > 0` is `θ² / V_T(u, v)`. -/
theorem isLeast_perturbation_sum_sq (P : MarkovKernel V) {u v : V} (huv : u ≠ v)
    {T : ℕ} (hT : 1 ≤ T) {θ : ℝ} (hθ : 0 < θ) :
    IsLeast {E : ℝ | ∃ ζ : ℕ → V → ℝ,
      θ ≤ |∑ s ∈ Icc 1 T, ∑ z, differenceRow P u v (T - s) z * ζ s z| ∧
      E = ∑ s ∈ Icc 1 T, ∑ z, ζ s z ^ 2}
      (θ ^ 2 / normalizedVariance P u v T) := by
  have hV : 0 < normalizedVariance P u v T := normalizedVariance_pos P huv hT
  constructor
  · obtain ⟨hresponse, hsq⟩ := aligned_perturbation_attains P hV θ
    exact ⟨fun s z => θ / normalizedVariance P u v T * differenceRow P u v (T - s) z,
      by rw [hresponse, abs_of_pos hθ], hsq.symm⟩
  · rintro E ⟨ζ, hresponse, rfl⟩
    apply (div_le_iff₀ hV).mpr
    have hsq := (sq_le_sq₀ hθ.le (abs_nonneg _)).mpr hresponse
    rw [sq_abs] at hsq
    simpa only [mul_comm] using hsq.trans (perturbation_response_sq_le P u v T ζ)

end GraphStability
