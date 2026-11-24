import GraphStability.Transport
import GraphStability.GaussianLaw

/-!
# Averaging with Gaussian noise (equation (S14))

`GaussianAveragingProcess` is the process of Section T2.1; `GaussianNoise`
proves that one exists.
-/

open MeasureTheory ProbabilityTheory

namespace GraphStability

variable {V : Type*} [Fintype V]

/-- Averaging with fresh independent Gaussian noise, started from zero. The
accessor `ξ` uses the round numbering `ξ₁, ξ₂, …` of the paper. -/
structure GaussianAveragingProcess (P : MarkovKernel V) (σ : ℝ) (Ω : Type*)
    [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] where
  /-- `noise t x` is the noise added at vertex `x` in round `t + 1`. -/
  noise : ℕ → V → Ω → ℝ
  /-- `f t x` is the value at vertex `x` after `t` rounds. -/
  f : ℕ → V → Ω → ℝ
  /-- Every noise coordinate is measurable. -/
  noise_measurable : ∀ t x, Measurable (noise t x)
  /-- Every noise coordinate is Gaussian with mean zero and variance `σ²`. -/
  noise_law : ∀ t x, Measure.map (noise t x) volume = gaussianReal 0 (σ ^ 2).toNNReal
  /-- The noise is independent across rounds and vertices. -/
  noise_indep : iIndepFun (fun (p : ℕ × V) => noise p.1 p.2) volume
  /-- The initial values are zero. -/
  f_zero : ∀ x, f 0 x = 0
  /-- One round: average by `P`, then add the fresh noise. -/
  f_succ : ∀ t x ω, f (t + 1) x ω = markovOperator P (fun y => f t y ω) x + noise t x ω

variable {P : MarkovKernel V} {σ : ℝ} {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (volume : Measure Ω)]

omit [Fintype V] in
/-- Re-indexing a finite sum over rounds `t ≥ 1` by the noise indices `t - 1`
does not change it. -/
theorem sum_image_pred_fst {M : Type*} [AddCommMonoid M] [DecidableEq V]
    (S : Finset (ℕ × V)) (hS : ∀ p ∈ S, 1 ≤ p.1) (g : ℕ × V → M) :
    ∑ q ∈ S.image (fun p : ℕ × V => (p.1 - 1, p.2)), g (q.1 + 1, q.2) =
      ∑ p ∈ S, g p := by
  have hinv : Set.LeftInvOn (fun q : ℕ × V => (q.1 + 1, q.2))
      (fun p : ℕ × V => (p.1 - 1, p.2)) S := by
    intro p hp
    exact Prod.ext (Nat.sub_add_cancel (hS p hp)) rfl
  rw [Finset.sum_image hinv.injOn]
  exact Finset.sum_congr rfl fun p hp => congrArg g (hinv hp)

namespace GaussianAveragingProcess

/-- The noise of round `t`, in the numbering of the paper: `ξ t = noise (t - 1)`.
Only the rounds `t ≥ 1` occur in the process. -/
def ξ (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) : V → Ω → ℝ :=
  proc.noise (t - 1)

/-- Each noise coordinate has the same distribution as the identity under `N(0, σ²)`. -/
theorem noise_identDistrib (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) :
    IdentDistrib (proc.noise t x) id volume (gaussianReal 0 (σ ^ 2).toNNReal) :=
  ⟨(proc.noise_measurable t x).aemeasurable, measurable_id.aemeasurable,
    by simpa only [Measure.map_id] using proc.noise_law t x⟩

/-- The update rule in the numbering of the paper:
`f_{t+1} = P f_t + ξ_{t+1}`. -/
theorem f_update (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) (ω : Ω) :
    proc.f (t + 1) x ω = markovOperator P (fun y => proc.f t y ω) x + proc.ξ (t + 1) x ω :=
  proc.f_succ t x ω

/-- Each noise coordinate has a finite second moment. -/
theorem noise_memLp_two (proc : GaussianAveragingProcess P σ Ω) (p : ℕ × V) :
    MemLp (proc.noise p.1 p.2) 2 volume :=
  (proc.noise_identDistrib p.1 p.2).memLp_iff.mpr (memLp_id_gaussianReal 2)

/-- Every fresh-noise coordinate `ξ t x` has expectation `0`. -/
theorem ξ_integral_zero (proc : GaussianAveragingProcess P σ Ω) (t : ℕ) (x : V) :
    ∫ ω, proc.ξ t x ω = 0 :=
  (proc.noise_identDistrib (t - 1) x).integral_eq.trans integral_id_gaussianReal

/-- A finite linear combination of the fresh noise from rounds `t ≥ 1` is
Gaussian with mean zero and variance `σ²` times the sum of the squared
coefficients. -/
theorem ξ_linear_combination_law (proc : GaussianAveragingProcess P σ Ω) (S : Finset (ℕ × V))
    (hS : ∀ p ∈ S, 1 ≤ p.1) (c : ℕ × V → ℝ) :
    Measure.map (fun ω => ∑ p ∈ S, c p * proc.ξ p.1 p.2 ω) volume =
      gaussianReal 0 (σ ^ 2 * ∑ p ∈ S, c p ^ 2).toNNReal := by
  classical
  let e : ℕ × V → ℕ × V := fun p => (p.1 - 1, p.2)
  let c' : ℕ × V → ℝ := fun q => c (q.1 + 1, q.2)
  have hfun : (fun ω => ∑ p ∈ S, c p * proc.ξ p.1 p.2 ω)
      = fun ω => ∑ q ∈ S.image e, c' q * proc.noise q.1 q.2 ω := by
    funext ω
    exact (sum_image_pred_fst S hS (fun p => c p * proc.ξ p.1 p.2 ω)).symm
  have hvar : (∑ q ∈ S.image e, (c' q ^ 2).toNNReal * (σ ^ 2).toNNReal)
      = ∑ p ∈ S, (c p ^ 2).toNNReal * (σ ^ 2).toNNReal :=
    sum_image_pred_fst S hS (fun p => (c p ^ 2).toNNReal * (σ ^ 2).toNNReal)
  rw [hfun, gaussian_linear_combination_law (S.image e) (fun q => proc.noise q.1 q.2) c'
    (fun _ => (σ ^ 2).toNNReal) proc.noise_indep
    (fun q => proc.noise_measurable q.1 q.2) (fun q _ => proc.noise_law q.1 q.2), hvar]
  have hsq : ∀ p ∈ S, (0 : ℝ) ≤ c p ^ 2 := fun p _ => sq_nonneg _
  rw [← Finset.sum_mul, ← Real.toNNReal_sum_of_nonneg hsq,
    ← Real.toNNReal_mul (Finset.sum_nonneg hsq), mul_comm]

end GaussianAveragingProcess

end GraphStability
