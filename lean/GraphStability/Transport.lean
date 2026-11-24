import Mathlib.Combinatorics.SimpleGraph.Metric
import GraphStability.FiniteTransport.ProbabilityMatrices

/-!
# Graph distance, transport distance, and discrete Ricci curvature (Section T1.2)

The graph distance is `SimpleGraph.dist`, which is a metric when the graph is
connected.
-/

noncomputable section

namespace GraphStability

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V)

/-- The graph distance `d(x, y)`, as a real number. -/
def graphDistance (x y : V) : ℝ := (G.dist x y : ℝ)

/-- The 1-Wasserstein distance `W₁(μ, ν)` for the graph distance: the infimum
of the transport cost over all transport plans between `μ` and `ν`. -/
def wasserstein1 (μ ν : PMF V) : ℝ :=
  sInf {r | ∃ π : PMF (V × V),
    r = (∑ p : V × V, graphDistance G p.1 p.2 * (π p).toReal) ∧
    π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- A Markov kernel on `V`: a probability distribution on `V` for each element
of `V`. -/
def MarkovKernel (V : Type*) := V → PMF V

/-- One averaging step, `(Pg)(x) = ∑_z P_xz g(z)`. -/
def markovOperator (P : MarkovKernel V) (g : V → ℝ) : V → ℝ :=
  fun x => ∑ z, (P x z).toReal * g z

/-- The discrete Ricci curvature `1 - W₁(P x, P y) / d(x, y)` of a pair of
vertices. -/
def ricciCurvature (P : MarkovKernel V) (x y : V) : ℝ :=
  1 - wasserstein1 G (P x) (P y) / graphDistance G x y

/-- On an edge, curvature is `1 - W₁` because the graph distance is one. -/
theorem ricciCurvature_eq_one_sub_wasserstein_of_adj
    {G : SimpleGraph V} {P : MarkovKernel V} {u v : V}
    (hadj : G.Adj u v) :
    ricciCurvature G P u v = 1 - wasserstein1 G (P u) (P v) := by
  simp [ricciCurvature, graphDistance, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]

/-- A function on the vertices is 1-Lipschitz for the graph distance:
`|g x - g y| ≤ d(x, y)` for all vertices `x` and `y`. -/
def IsOneLipschitz (g : V → ℝ) : Prop :=
  ∀ x y, |g x - g y| ≤ graphDistance G x y

omit [Fintype V] in
/-- It suffices to bound the differences `g x - g y` from above. -/
theorem isOneLipschitz_of_sub_le {G : SimpleGraph V} {g : V → ℝ}
    (hg : ∀ x y, g x - g y ≤ graphDistance G x y) : IsOneLipschitz G g := by
  intro x y
  have h := hg y x
  rw [graphDistance, SimpleGraph.dist_comm] at h
  exact abs_sub_le_iff.mpr ⟨hg x y, h⟩

/-- Every transport plan between `μ` and `ν` gives an upper bound on `W₁(μ, ν)`. -/
theorem wasserstein1_le_transportPlan_cost (μ ν : PMF V) (π : PMF (V × V))
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν) :
    wasserstein1 G μ ν ≤ ∑ p, graphDistance G p.1 p.2 * (π p).toReal := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨π, rfl, _, _⟩
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  · exact ⟨π, rfl, hfst, hsnd⟩

variable {G : SimpleGraph V}

/-- The 1-Wasserstein distance `W₁(μ, ν)` is non-negative. -/
theorem wasserstein1_nonneg (μ ν : PMF V) : 0 ≤ wasserstein1 G μ ν := by
  apply Real.sInf_nonneg
  rintro _ ⟨π, rfl, _, _⟩
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

omit [Fintype V] in
/-- On a connected graph, if `|f x - f y| ≤ L` on every edge, then
`|f x - f y| ≤ L d(x, y)` for all vertices `x` and `y`. -/
theorem abs_sub_le_mul_dist_of_adj (hG : G.Connected) (f : V → ℝ) (L : ℝ)
    (hedge : ∀ x y, G.Adj x y → |f x - f y| ≤ L) (x y : V) :
    |f x - f y| ≤ L * graphDistance G x y := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  rw [graphDistance, ← hp]
  clear hp
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
      calc
        |f x - f y| ≤ |f x - f z| + |f z - f y| := abs_sub_le _ _ _
        _ ≤ L + L * (p.length : ℝ) := add_le_add (hedge x z hxz) ih
        _ = L * ((SimpleGraph.Walk.cons hxz p).length : ℝ) := by
          rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Summing `g p.1` against a transport plan equals summing `g` against its
first marginal. -/
theorem sum_transportPlan_fst (π : PMF (V × V)) {μ : PMF V}
    (hfst : π.map Prod.fst = μ) (g : V → ℝ) :
    ∑ p : V × V, g p.1 * (π p).toReal = ∑ x, g x * (μ x).toReal := by
  subst hfst
  simp only [FiniteTransport.map_fst_toReal, Finset.mul_sum, Fintype.sum_prod_type]

/-- Summing `g p.2` against a transport plan equals summing `g` against its
second marginal. -/
theorem sum_transportPlan_snd (π : PMF (V × V)) {ν : PMF V}
    (hsnd : π.map Prod.snd = ν) (g : V → ℝ) :
    ∑ p : V × V, g p.2 * (π p).toReal = ∑ x, g x * (ν x).toReal := by
  subst hsnd
  simp only [FiniteTransport.map_snd_toReal, Finset.mul_sum, Fintype.sum_prod_type_right]

/-- For a 1-Lipschitz function, the absolute difference between its averages
under `μ` and `ν` is at most `W₁(μ, ν)`. -/
theorem abs_pairing_le_wasserstein1 (μ ν : PMF V) (g : V → ℝ) (hg : IsOneLipschitz G g) :
    |(∑ x, (μ x).toReal * g x) - (∑ x, (ν x).toReal * g x)| ≤ wasserstein1 G μ ν := by
  simp only [mul_comm _ (g _)]
  refine le_csInf ?_ ?_
  · obtain ⟨π, hfst, hsnd⟩ := FiniteTransport.exists_pmf_map_fst_snd μ ν
    exact ⟨_, π, rfl, hfst, hsnd⟩
  · rintro r ⟨π, rfl, hfst, hsnd⟩
    have hpair : (∑ x, g x * (μ x).toReal) - (∑ x, g x * (ν x).toReal)
        = ∑ p : V × V, (g p.1 - g p.2) * (π p).toReal := by
      simp only [sub_mul, Finset.sum_sub_distrib, sum_transportPlan_fst π hfst g,
        sum_transportPlan_snd π hsnd g]
    rw [hpair]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_right (hg p.1 p.2) ENNReal.toReal_nonneg

end GraphStability
