import Mathlib.Probability.HasLawExists
import GraphStability.Process

/-!
# Existence of the process (equation (S14))

A family of independent Gaussian variables indexed by rounds and vertices
supplies the noise, and the update rule then defines the vertex values.
-/

open MeasureTheory ProbabilityTheory

namespace GraphStability

universe uV

variable {V : Type uV} [Fintype V]

/-- A process exists for every kernel and every noise amplitude. -/
theorem exists_gaussianAveragingProcess (P : MarkovKernel V) (σ : ℝ) :
    ∃ (Ω : Type uV) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (volume : Measure Ω)),
      Nonempty (GaussianAveragingProcess P σ Ω) := by
  obtain ⟨Ω, m, μ, X, hm, hlaw, hind, hμ⟩ :=
    exists_iid (ℕ × V) (gaussianReal 0 (σ ^ 2).toNNReal)
  letI : MeasureSpace Ω := { toMeasurableSpace := m, volume := μ }
  haveI : IsProbabilityMeasure (volume : Measure Ω) := hμ
  let values := Nat.rec (motive := fun _ => V → Ω → ℝ) (fun _ _ => 0)
    (fun t prev x ω => markovOperator P (fun y => prev y ω) x + X (t, x) ω)
  exact ⟨Ω, inferInstance, inferInstance, ⟨
    { noise := fun t x => X (t, x)
      f := values
      noise_measurable := fun t x => hm (t, x)
      noise_law := fun t x => (hlaw (t, x)).map_eq
      noise_indep := hind
      f_zero := fun _ => rfl
      f_succ := fun _ _ _ => rfl }⟩⟩

end GraphStability
