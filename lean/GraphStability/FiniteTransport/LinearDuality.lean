import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-!
# Finite transport duality from separation (Lemma T1.1)

The image of the probability simplex under the map recording both marginals and
the transport cost is compact and convex. Separating a point below the cost of
every transport plan yields two potentials `α` and `β` with `α + β ≤ c`.
-/

namespace GraphStability.FiniteTransport

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The two marginals and the cost of a real transport matrix. -/
def marginalCost (c : ι → κ → ℝ) :
    ((ι × κ) → ℝ) →ₗ[ℝ] ((ι → ℝ) × (κ → ℝ) × ℝ) where
  toFun w := (fun i => ∑ j, w (i, j),
    fun j => ∑ i, w (i, j), ∑ p, c p.1 p.2 * w p)
  map_add' w z := by
    ext <;> simp [Finset.sum_add_distrib, mul_add]
  map_smul' a w := by
    ext <;> simp [Finset.mul_sum, mul_left_comm]

/-- A point mass records its two endpoints and their transport cost. -/
theorem marginalCost_single [DecidableEq ι] [DecidableEq κ] (c : ι → κ → ℝ) (i : ι) (j : κ) :
    marginalCost c (Pi.single (i, j) 1) =
      (Pi.single i 1, Pi.single j 1, c i j) := by
  ext <;> simp [marginalCost, Pi.single_apply, ite_and,
    Fintype.sum_prod_type]

/-- Coordinates of a linear functional on the marginal-and-cost space. -/
theorem linear_form_coordinates [DecidableEq ι] [DecidableEq κ]
    (f : ((ι → ℝ) × (κ → ℝ) × ℝ) →ₗ[ℝ] ℝ)
    (μ : ι → ℝ) (ν : κ → ℝ) (t : ℝ) :
    f (μ, ν, t) =
      (∑ i, μ i * f (Pi.single i 1, 0, 0)) +
      (∑ j, ν j * f (0, Pi.single j 1, 0)) + t * f (0, 0, 1) := by
  have hsplit : (μ, ν, t) =
      (∑ i, μ i • (Pi.single (M := fun _ : ι => ℝ) i 1, (0 : κ → ℝ), (0 : ℝ))) +
      (∑ j, ν j • ((0 : ι → ℝ), Pi.single (M := fun _ : κ => ℝ) j 1, (0 : ℝ))) +
      t • (0, 0, 1) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hsplit, map_add, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- For marginals `μ` and `ν` in the standard simplex, every strict lower bound
on the transport cost of all feasible probability matrices is exceeded by the
dual objective of a pair of potentials `α` and `β` with `α i + β j ≤ c i j`. -/
theorem exists_transport_dual (c : ι → κ → ℝ)
    {μ : ι → ℝ} {ν : κ → ℝ}
    (hμ : μ ∈ stdSimplex ℝ ι) (hν : ν ∈ stdSimplex ℝ κ)
    {r : ℝ}
    (hr : ∀ w : (ι × κ) → ℝ, w ∈ stdSimplex ℝ (ι × κ) →
      (∀ i, ∑ j, w (i, j) = μ i) →
      (∀ j, ∑ i, w (i, j) = ν j) →
      r < ∑ p, c p.1 p.2 * w p) :
    ∃ α : ι → ℝ, ∃ β : κ → ℝ,
      (∀ i j, α i + β j ≤ c i j) ∧
      r < (∑ i, μ i * α i) + ∑ j, ν j * β j := by
  classical
  have hnot : (μ, ν, r) ∉ marginalCost c '' stdSimplex ℝ (ι × κ) := by
    rintro ⟨w, hw, heq⟩
    obtain ⟨hrow, hrest⟩ := Prod.mk.inj heq
    obtain ⟨hcol, hcost⟩ := Prod.mk.inj hrest
    exact (hr w hw (congrFun hrow) (congrFun hcol)).ne hcost.symm
  obtain ⟨f, s, hbelow, habove⟩ := geometric_hahn_banach_point_closed
    ((convex_stdSimplex ℝ _).linear_image (marginalCost c))
    ((isCompact_stdSimplex _).image (marginalCost c).continuous_of_finiteDimensional).isClosed hnot
  let a : ι → ℝ := fun i => f (Pi.single i 1, 0, 0)
  let b : κ → ℝ := fun j => f (0, Pi.single j 1, 0)
  let γ : ℝ := f (0, 0, 1)
  have hformula (μ' : ι → ℝ) (ν' : κ → ℝ) (t : ℝ) :
      f (μ', ν', t) = (∑ i, μ' i * a i) + (∑ j, ν' j * b j) + t * γ :=
    linear_form_coordinates f.toLinearMap μ' ν' t
  rw [hformula] at hbelow
  -- The product plan has the prescribed marginals and cost greater than `r`, so `γ > 0`.
  let w₀ : (ι × κ) → ℝ := fun p => μ p.1 * ν p.2
  have hrow (i : ι) : ∑ j, w₀ (i, j) = μ i := by simp [w₀, ← Finset.mul_sum, hν.2]
  have hcol (j : κ) : ∑ i, w₀ (i, j) = ν j := by simp [w₀, ← Finset.sum_mul, hμ.2]
  have hw₀ : w₀ ∈ stdSimplex ℝ (ι × κ) :=
    ⟨fun p => mul_nonneg (hμ.1 p.1) (hν.1 p.2), by
      simpa only [Fintype.sum_prod_type, hrow] using hμ.2⟩
  have hsep₀ := habove (μ, ν, ∑ p : ι × κ, c p.1 p.2 * w₀ p)
    ⟨w₀, hw₀, Prod.ext (funext hrow) (Prod.ext (funext hcol) rfl)⟩
  rw [hformula] at hsep₀
  have hγ : 0 < γ := by
    refine pos_of_mul_pos_right ?_ (sub_nonneg.mpr (hr w₀ hw₀ hrow hcol).le)
    rw [sub_mul, sub_pos]
    exact lt_of_add_lt_add_left (hbelow.trans hsep₀)
  have hvertex (i : ι) (j : κ) : s < a i + b j + c i j * γ := by
    have h := habove (marginalCost c (Pi.single (i, j) 1))
      ⟨Pi.single (i, j) 1, single_mem_stdSimplex ℝ (i, j), rfl⟩
    rw [marginalCost_single, hformula] at h
    simpa [Pi.single_apply] using h
  refine ⟨fun i => (s - a i) / γ, fun j => -b j / γ, ?_, ?_⟩
  · intro i j
    rw [← add_div, div_le_iff₀ hγ]
    linarith [hvertex i j]
  · have hvalue :
        (∑ i, μ i * ((s - a i) / γ)) + (∑ j, ν j * (-b j / γ)) =
          (s - (∑ i, μ i * a i) - ∑ j, ν j * b j) / γ := by
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, ← Finset.sum_div]
      simp only [mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hμ.2, one_mul, mul_neg, Finset.sum_neg_distrib]
      ring
    rw [hvalue, lt_div_iff₀ hγ]
    linarith

end GraphStability.FiniteTransport
