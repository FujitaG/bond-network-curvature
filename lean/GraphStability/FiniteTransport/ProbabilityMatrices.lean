import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Transport plans as finite probability matrices (equation (S3))
-/

namespace GraphStability.FiniteTransport

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The real probability weights of a finite `PMF` lie in the standard
simplex. -/
theorem pmf_mem_simplex (μ : PMF ι) :
    (fun i => (μ i).toReal) ∈ stdSimplex ℝ ι := by
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_⟩
  simpa only [tsum_fintype, ENNReal.toReal_sum (fun i _ => μ.apply_ne_top i),
    ENNReal.toReal_one] using congrArg ENNReal.toReal μ.tsum_coe

/-- The `PMF` defined by a point in the standard simplex. -/
def pmfOfSimplex (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw.1 i), hw.2,
      ENNReal.ofReal_one])

/-- Conversion to a `PMF` preserves each real coordinate. -/
theorem pmfOfSimplex_toReal (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι) (i : ι) :
    (pmfOfSimplex w hw i).toReal = w i :=
  ENNReal.toReal_ofReal (hw.1 i)

/-- The first marginal of a joint `PMF` is given by its row sums. -/
theorem map_fst_toReal (π : PMF (ι × κ)) (i : ι) :
    ((π.map Prod.fst) i).toReal = ∑ j, (π (i, j)).toReal := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type_right, Fintype.sum_ite_eq]
  exact ENNReal.toReal_sum (fun j _ => π.apply_ne_top (i, j))

/-- The second marginal of a joint `PMF` is given by its column sums. -/
theorem map_snd_toReal (π : PMF (ι × κ)) (j : κ) :
    ((π.map Prod.snd) j).toReal = ∑ i, (π (i, j)).toReal := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_ite_eq]
  exact ENNReal.toReal_sum (fun i _ => π.apply_ne_top (i, j))

/-- A probability matrix with row sums `μ` has first marginal `μ`. -/
theorem pmfOfSimplex_map_fst (w : (ι × κ) → ℝ)
    (hw : w ∈ stdSimplex ℝ (ι × κ)) (μ : PMF ι)
    (hrow : ∀ i, ∑ j, w (i, j) = (μ i).toReal) :
    (pmfOfSimplex w hw).map Prod.fst = μ := by
  ext i
  apply (ENNReal.toReal_eq_toReal
    (((pmfOfSimplex w hw).map Prod.fst).apply_ne_top i) (μ.apply_ne_top i)).mp
  simpa only [map_fst_toReal, pmfOfSimplex_toReal] using hrow i

/-- A probability matrix with column sums `ν` has second marginal `ν`. -/
theorem pmfOfSimplex_map_snd (w : (ι × κ) → ℝ)
    (hw : w ∈ stdSimplex ℝ (ι × κ)) (ν : PMF κ)
    (hcol : ∀ j, ∑ i, w (i, j) = (ν j).toReal) :
    (pmfOfSimplex w hw).map Prod.snd = ν := by
  ext j
  apply (ENNReal.toReal_eq_toReal
    (((pmfOfSimplex w hw).map Prod.snd).apply_ne_top j) (ν.apply_ne_top j)).mp
  simpa only [map_snd_toReal, pmfOfSimplex_toReal] using hcol j

omit [Fintype ι] [Fintype κ] in
/-- Any two distributions are the marginals of some joint distribution (their product). -/
theorem exists_pmf_map_fst_snd (μ : PMF ι) (ν : PMF κ) :
    ∃ π : PMF (ι × κ), π.map Prod.fst = μ ∧ π.map Prod.snd = ν := by
  refine ⟨μ.bind (fun i => ν.map (Prod.mk i)), ?_, ?_⟩ <;>
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_const, PMF.bind_pure]

end GraphStability.FiniteTransport
