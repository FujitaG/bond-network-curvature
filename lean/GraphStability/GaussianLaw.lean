import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Linear combinations of independent Gaussian variables (Lemma T2.1)
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace GraphStability

variable {ι Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (volume : Measure Ω)]

/-- A finite sum of independent centred Gaussian variables is centred Gaussian,
with variance the sum of their variances. -/
theorem gaussian_finset_sum_law (S : Finset ι)
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hindep : iIndepFun X volume) (hmeas : ∀ i, Measurable (X i))
    (hgauss : ∀ i ∈ S, Measure.map (X i) volume = gaussianReal 0 (v i)) :
    Measure.map (fun ω => ∑ i ∈ S, X i ω) volume = gaussianReal 0 (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hsum := ih (fun j hj => hgauss j (Finset.mem_insert_of_mem hj))
      have hiLaw := hgauss i (Finset.mem_insert_self i S)
      have hind' : IndepFun (fun ω => ∑ j ∈ S, X j ω) (X i) volume := by
        simpa only [Finset.sum_fn] using hindep.indepFun_finset_sum_of_notMem hmeas hi
      have hadd := gaussianReal_add_gaussianReal_of_indepFun hind' hsum hiLaw
      simpa only [Finset.sum_insert hi, Pi.add_apply, add_comm, add_zero] using hadd

/-- A finite linear combination `∑ c_i X_i` of independent centred Gaussian
variables is centred Gaussian, with variance `∑ c_i² v_i`. -/
theorem gaussian_linear_combination_law (S : Finset ι)
    (X : ι → Ω → ℝ) (c : ι → ℝ) (v : ι → ℝ≥0)
    (hindep : iIndepFun X volume) (hmeas : ∀ i, Measurable (X i))
    (hgauss : ∀ i ∈ S, Measure.map (X i) volume = gaussianReal 0 (v i)) :
    Measure.map (fun ω => ∑ i ∈ S, c i * X i ω) volume =
      gaussianReal 0 (∑ i ∈ S, (c i ^ 2).toNNReal * v i) := by
  refine gaussian_finset_sum_law S (fun i ω => c i * X i ω)
    (fun i => (c i ^ 2).toNNReal * v i) ?_ ?_ ?_
  · exact hindep.comp (fun i x => c i * x) (fun _ => measurable_const.mul measurable_id)
  · exact fun i => (hmeas i).const_mul (c i)
  · intro i hi
    calc
      Measure.map (fun ω => c i * X i ω) volume =
          Measure.map (fun x : ℝ => c i * x) (Measure.map (X i) volume) :=
        (Measure.map_map (measurable_const.mul measurable_id) (hmeas i)).symm
      _ = gaussianReal 0 ((c i ^ 2).toNNReal * v i) := by
        rw [hgauss i hi]
        simpa only [Real.toNNReal_of_nonneg (sq_nonneg (c i)), mul_zero] using
          (gaussianReal_map_const_mul (μ := 0) (v := v i) (c i))

end GraphStability
