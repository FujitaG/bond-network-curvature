import GraphStability.FiniteTransport.LinearDuality
import GraphStability.FiniteTransport.CostTransform
import GraphStability.Transport

/-!
# Duality for transport distance (equation (S4), Lemma T1.1)

On a finite connected graph, for every `r < W₁(μ, ν)` there is a 1-Lipschitz
function `g` whose pairing `∑_z g(z) (μ(z) - ν(z))` exceeds `r`: the proof
separates `(μ, ν, r)` from the convex set of attainable triples of two
marginals and a cost, and applies the cost transform to the resulting
potentials. The feasible probability matrices form a compact set, so the
minimum transport cost is attained. The 1-Lipschitz functions vanishing at a
fixed vertex also form a compact set, so their maximum pairing is attained, and
it equals the 1-Wasserstein distance `W₁`.
-/

namespace GraphStability

open FiniteTransport

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V}

/-- Every strict lower bound on `W₁(μ, ν)` is exceeded by the pairing of some
1-Lipschitz function. -/
theorem exists_lipschitz_function_gt (hG : G.Connected) (μ ν : PMF V)
    {r : ℝ} (hr : r < wasserstein1 G μ ν) :
    ∃ g : V → ℝ, IsOneLipschitz G g ∧
      r < (∑ x, (μ x).toReal * g x) - (∑ x, (ν x).toReal * g x) := by
  obtain ⟨α, β, hfeasible, hvalue⟩ := exists_transport_dual (graphDistance G)
    (pmf_mem_simplex μ) (pmf_mem_simplex ν) (r := r) (fun w hw hrow hcol => by
      have hle := wasserstein1_le_transportPlan_cost G μ ν (pmfOfSimplex w hw)
        (pmfOfSimplex_map_fst w hw μ hrow) (pmfOfSimplex_map_snd w hw ν hcol)
      simpa only [pmfOfSimplex_toReal] using hr.trans_le hle)
  have htriangle (x y z : V) :
      graphDistance G x z ≤ graphDistance G x y + graphDistance G y z := by
    dsimp [graphDistance]
    exact_mod_cast hG.dist_triangle (u := x) (v := y) (w := z)
  have hself (x : V) : graphDistance G x x = 0 := by simp [graphDistance]
  refine ⟨costTransform (graphDistance G) β,
    isOneLipschitz_of_sub_le (costTransform_sub_le (graphDistance G) htriangle β),
    hvalue.trans_le ?_⟩
  exact pairing_le_costTransform (graphDistance G) hself α β
    (fun x => (μ x).toReal) (fun x => (ν x).toReal)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hfeasible

omit [Fintype V] in
/-- The 1-Lipschitz functions vanishing at a fixed vertex form a compact set. -/
theorem isCompact_normalized_isOneLipschitz (G : SimpleGraph V) (x₀ : V) :
    IsCompact {g : V → ℝ | IsOneLipschitz G g ∧ g x₀ = 0} := by
  have hclosed_increments :
      IsClosed {g : V → ℝ | ∀ x y, |g x - g y| ≤ graphDistance G x y} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((continuous_apply x).sub (continuous_apply y)).abs continuous_const
  have hclosed : IsClosed {g : V → ℝ | IsOneLipschitz G g ∧ g x₀ = 0} :=
    hclosed_increments.inter
      (isClosed_eq (continuous_apply x₀)
        (continuous_const : Continuous fun _ : V → ℝ => (0 : ℝ)))
  have hbound (g : V → ℝ) (hg : IsOneLipschitz G g ∧ g x₀ = 0) (x : V) :
      |g x| ≤ graphDistance G x₀ x := by
    simpa [hg.2] using hg.1 x₀ x
  have hbox : IsCompact
      (Set.Icc (fun x => -graphDistance G x₀ x) (fun x => graphDistance G x₀ x)) := isCompact_Icc
  apply hbox.of_isClosed_subset hclosed
  intro g hg
  exact ⟨fun x => neg_le_of_abs_le (hbound g hg x),
    fun x => le_of_abs_le (hbound g hg x)⟩

/-- Equation (S4): the 1-Wasserstein distance `W₁(μ, ν)` is attained by a
transport plan between `μ` and `ν`. -/
theorem exists_optimal_transportPlan (G : SimpleGraph V) (μ ν : PMF V) :
    ∃ π : PMF (V × V), π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      wasserstein1 G μ ν = ∑ p, graphDistance G p.1 p.2 * (π p).toReal := by
  let S : Set ((V × V) → ℝ) := stdSimplex ℝ (V × V) ∩
    ({w | ∀ x, ∑ y, w (x, y) = (μ x).toReal} ∩
     {w | ∀ y, ∑ x, w (x, y) = (ν y).toReal})
  let cost : ((V × V) → ℝ) → ℝ := fun w => ∑ p, graphDistance G p.1 p.2 * w p
  have hcompact : IsCompact S := by
    unfold S
    apply (isCompact_stdSimplex _).inter_right
    apply IsClosed.inter <;> simp only [Set.setOf_forall] <;>
      exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  have hmem : ∀ ρ : PMF (V × V), ρ.map Prod.fst = μ → ρ.map Prod.snd = ν →
      (fun p => (ρ p).toReal) ∈ S := by
    intro ρ hρfst hρsnd
    exact ⟨pmf_mem_simplex ρ, fun x => by rw [← hρfst, map_fst_toReal],
      fun y => by rw [← hρsnd, map_snd_toReal]⟩
  have hnonempty : S.Nonempty := by
    obtain ⟨ρ, hρfst, hρsnd⟩ := exists_pmf_map_fst_snd μ ν
    exact ⟨_, hmem ρ hρfst hρsnd⟩
  have hcost : Continuous cost := by fun_prop
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn hnonempty hcost.continuousOn
  let π := pmfOfSimplex w hw.1
  have hfst : π.map Prod.fst = μ :=
    pmfOfSimplex_map_fst w hw.1 μ hw.2.1
  have hsnd : π.map Prod.snd = ν :=
    pmfOfSimplex_map_snd w hw.1 ν hw.2.2
  refine ⟨π, hfst, hsnd, IsLeast.csInf_eq ?_⟩
  refine ⟨⟨π, rfl, hfst, hsnd⟩, ?_⟩
  rintro r ⟨ρ, rfl, hρfst, hρsnd⟩
  have hminimum : cost w ≤ cost (fun p => (ρ p).toReal) := hmin (hmem ρ hρfst hρsnd)
  simpa only [cost, π, pmfOfSimplex_toReal] using hminimum

/-- Subtracting a constant does not change the pairing, because both
distributions have total mass one. -/
private theorem pairing_sub_constant (μ ν : PMF V) (g : V → ℝ) (c : ℝ) :
    (∑ x, (μ x).toReal * (g x - c)) - (∑ x, (ν x).toReal * (g x - c)) =
      (∑ x, (μ x).toReal * g x) - (∑ x, (ν x).toReal * g x) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [(pmf_mem_simplex μ).2, (pmf_mem_simplex ν).2]
  ring

/-- On a connected graph, some 1-Lipschitz function attains `W₁(μ, ν)`. -/
theorem exists_optimal_lipschitz_function (hG : G.Connected) (μ ν : PMF V) :
    ∃ g : V → ℝ, IsOneLipschitz G g ∧
      wasserstein1 G μ ν =
        (∑ x, (μ x).toReal * g x) - (∑ x, (ν x).toReal * g x) := by
  obtain ⟨x₀⟩ := hG.nonempty
  let S : Set (V → ℝ) := {g | IsOneLipschitz G g ∧ g x₀ = 0}
  let L : (V → ℝ) → ℝ := fun g =>
    (∑ x, (μ x).toReal * g x) - (∑ x, (ν x).toReal * g x)
  have hzero : (fun _ : V => (0 : ℝ)) ∈ S := by
    simp [S, IsOneLipschitz, graphDistance]
  have hL : Continuous L := by fun_prop
  obtain ⟨g, hg, hmax⟩ := (isCompact_normalized_isOneLipschitz G x₀).exists_isMaxOn
    ⟨fun _ => 0, hzero⟩ hL.continuousOn
  refine ⟨g, hg.1, le_antisymm ?_ ?_⟩
  · refine le_of_forall_lt fun r hr => ?_
    obtain ⟨f, hf, hgreater⟩ := exists_lipschitz_function_gt hG μ ν hr
    have hnormalized : (fun x => f x - f x₀) ∈ S := by
      refine ⟨fun x y => ?_, sub_self _⟩
      simpa only [sub_sub_sub_cancel_right] using hf x y
    have hcomparison : L (fun x => f x - f x₀) ≤ L g := hmax hnormalized
    exact hgreater.trans_le ((pairing_sub_constant μ ν f (f x₀)).symm.trans_le hcomparison)
  · exact (le_abs_self _).trans (abs_pairing_le_wasserstein1 μ ν g hg.1)

/-- Lemma T1.1: `W₁(μ, ν)` is the maximum of `|∑_z g(z) (μ(z) - ν(z))|` over
all 1-Lipschitz functions `g`. -/
theorem isGreatest_abs_pairing (hG : G.Connected) (μ ν : PMF V) :
    IsGreatest {a : ℝ | ∃ g : V → ℝ, IsOneLipschitz G g ∧
      a = |∑ z, g z * ((μ z).toReal - (ν z).toReal)|}
      (wasserstein1 G μ ν) := by
  have hsum (g : V → ℝ) : ∑ z, g z * ((μ z).toReal - (ν z).toReal) =
      (∑ z, (μ z).toReal * g z) - (∑ z, (ν z).toReal * g z) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_comm]
  constructor
  · obtain ⟨g, hg, hvalue⟩ := exists_optimal_lipschitz_function hG μ ν
    exact ⟨g, hg, by rw [hsum, ← hvalue, abs_of_nonneg (wasserstein1_nonneg μ ν)]⟩
  · rintro a ⟨g, hg, rfl⟩
    rw [hsum]
    exact abs_pairing_le_wasserstein1 μ ν g hg

end GraphStability
