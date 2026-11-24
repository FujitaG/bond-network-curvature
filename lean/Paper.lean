import GraphStability
import RhombicFamily

/-!
# The results of the Supplementary Information

Every lemma, proposition, and theorem of the Supplementary Theory (Sections T1
and T2) and of Supplementary Methods M1 is restated here under its number in
the paper, together with the definitions and equations that these results
concern and all columns of Table S3 except the point-group symbols.
-/

noncomputable section

open GraphStability MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Matrix

namespace Paper

universe uΩ uV

/-! ## Standing assumptions and notation

Throughout Sections T1 and T2, `G` is a finite connected simple graph with at
least two vertices, and `hG` is the proof that `G` is connected. Because the
averaging rule requires every vertex to have a neighbour, every quantity built
from it takes `hG` as an argument. Read `P hG`, `κ hG u v`, `Vt hG u v t`,
`Vinf hG u v`, `κeff hG u v`, `M hG`, and `κeffMin hG` as `P`, `κ(e)`, `V_t(e)`,
`V_∞(e)`, `κ_eff(e)`, `M_G`, and `κ_eff^min`, with `e = (u, v)`. In Section T2
the paper takes the noise amplitude `σ` and the breaking threshold `θ` to be
positive and writes `Θ = θ/σ`; each statement displays the assumptions it uses.

* `P hG x` is the distribution of one step from `x`; its masses have type
  `ℝ≥0∞`, `(P hG x y).toReal` is the entry `P_xy` as a real number, and
  `kernelMatrix (P hG)` is the matrix of these entries (`equation_S2`).
* `markovOperator P g x` is `(Pg)(x) = ∑_z P_xz g(z)`; for the averaging rule,
  this operator is given by equation (S1) (`equation_S1`).
* `differenceRow P u v j z` is `(P^j)_uz - (P^j)_vz` (`equation_S19`).
* `IsLeast S a` and `IsGreatest S a` state that `a` belongs to `S` and is its
  least or greatest element, respectively.
* `volume` is the probability measure, and `volume.real A` is the probability
  of `A` as a real number. `gaussianReal 0 (a ^ 2).toNNReal` is the Gaussian law
  `N(0, a²)`; its variance argument is a non-negative real, hence `.toNNReal`.
* The mean lifetime takes values in `[0, ∞]`. `ENNReal.ofReal` embeds a
  non-negative real into `[0, ∞]`, and `.toReal` converts a finite value back
  to `ℝ`. -/

section Theory

variable {V : Type uV} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected)

include hG

/-! ## Section T1: negative discrete Ricci curvature and amplification -/

omit [DecidableEq V] in
/-- Every vertex has a neighbour (Section T1.1). -/
theorem degree_pos (x : V) : 0 < G.degree x :=
  hG.preconnected.degree_pos_of_nontrivial x

omit [DecidableEq V] in
/-- The graph has an edge (Section T1.1). -/
theorem edge_exists : G.edgeFinset.Nonempty :=
  SimpleGraph.edgeFinset_nonempty.2 fun h => SimpleGraph.not_connected_bot (h ▸ hG)

/-- The averaging rule `P` of equation (S2): stay with probability `1/2`,
otherwise move to a uniformly chosen neighbour. -/
abbrev P : MarkovKernel V := lazyKernel G (degree_pos hG)

/-- Equation (S1): one averaging step. -/
theorem equation_S1 (g : V → ℝ) (x : V) :
    markovOperator (P hG) g x =
      g x / 2 + (∑ y ∈ G.neighborFinset x, g y) / (2 * G.degree x) := by
  simp only [markovOperator, lazyKernel_toReal, lazyMass_split, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, Fintype.sum_ite_eq']
  rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, ← Finset.mul_sum]
  ring

/-- Equation (S2): the entries of the matrix `P`. -/
theorem equation_S2 (x y : V) :
    kernelMatrix (P hG) x y = (P hG x y).toReal ∧
    (P hG x y).toReal =
      if y = x then 1 / 2 else if G.Adj x y then 1 / (2 * (G.degree x : ℝ)) else 0 :=
  ⟨rfl, lazyKernel_toReal G _ x y⟩

omit [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] hG in
/-- Equation (S4): the 1-Wasserstein distance `W₁(μ, ν)` is the minimum
transport cost over all transport plans between `μ` and `ν`. A transport plan
(S3) is a distribution `π` on `V × V` with marginals `μ` and `ν`. -/
theorem equation_S4 (μ ν : PMF V) :
    IsLeast {c : ℝ | ∃ π : PMF (V × V), π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
        c = ∑ p : V × V, (G.dist p.1 p.2 : ℝ) * (π p).toReal}
      (wasserstein1 G μ ν) := by
  refine ⟨exists_optimal_transportPlan G μ ν, ?_⟩
  rintro c ⟨π, hμ, hν, rfl⟩
  exact wasserstein1_le_transportPlan_cost G μ ν π hμ hν

/-- The discrete Ricci curvature of the pair `(u, v)`; on an edge `e = (u, v)`
it is `κ(e)` of equation (S5). -/
abbrev κ (u v : V) : ℝ := ricciCurvature G (P hG) u v

/-- Equation (S5): on an edge `(u, v)`, the discrete Ricci curvature is
`1 - W₁(P u, P v)`. -/
theorem equation_S5 {u v : V} (huv : G.Adj u v) :
    κ hG u v = 1 - wasserstein1 G (P hG u) (P hG v) :=
  ricciCurvature_eq_one_sub_wasserstein_of_adj huv

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] hG in
/-- Equation (S7): `IsOneLipschitz G g` states that `g` is 1-Lipschitz with
respect to the graph distance. -/
theorem equation_S7 (g : V → ℝ) :
    IsOneLipschitz G g ↔ ∀ x y, |g x - g y| ≤ G.dist x y :=
  Iff.rfl

omit [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
/-- **Lemma T1.1** (duality for transport distance), equation (S8): `W₁(μ, ν)`
is the maximum of `|∑_z g(z) (μ(z) - ν(z))|` over all 1-Lipschitz functions `g`. -/
theorem lemma_T1_1 (μ ν : PMF V) :
    IsGreatest {a : ℝ | ∃ g : V → ℝ, IsOneLipschitz G g ∧
        a = |∑ z, g z * ((μ z).toReal - (ν z).toReal)|}
      (wasserstein1 G μ ν) :=
  isGreatest_abs_pairing hG μ ν

/-- **Theorem 1** (negative curvature and amplification modes), equation (S13):
the maximum of `|(Pg)(u) - (Pg)(v)|` over all 1-Lipschitz functions `g` is
`1 - κ(e)`, and `κ(e) < 0` if and only if some 1-Lipschitz `g` has
`|(Pg)(u) - (Pg)(v)| > 1`. -/
theorem theorem_1 {u v : V} (huv : G.Adj u v) :
    IsGreatest {a : ℝ | ∃ g : V → ℝ, IsOneLipschitz G g ∧
        a = |markovOperator (P hG) g u - markovOperator (P hG) g v|}
      (1 - κ hG u v) ∧
    (κ hG u v < 0 ↔ ∃ g : V → ℝ, IsOneLipschitz G g ∧
        1 < |markovOperator (P hG) g u - markovOperator (P hG) g v|) :=
  ⟨isGreatest_edge_amplification hG huv, negative_curvature_iff_edge_amplification hG huv⟩

/-! ## Sections T2.1 to T2.6: the process, effective curvature, and the lifetime -/

variable {σ θ : ℝ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Equation (S14): the values start at `f₀ = 0` and evolve by
`f_{t+1} = P f_t + ξ_{t+1}`, where `ξ_{t+1}` is the fresh noise of round
`t + 1` (`equation_S14_noise`). -/
theorem equation_S14 (proc : GaussianAveragingProcess (P hG) σ Ω) :
    (∀ x, proc.f 0 x = 0) ∧
    ∀ t x ω, proc.f (t + 1) x ω =
      markovOperator (P hG) (fun y => proc.f t y ω) x + proc.ξ (t + 1) x ω :=
  ⟨proc.f_zero, proc.f_update⟩

/-- The fresh noise of equation (S14): independent across rounds `t ≥ 1` and
vertices, with each component distributed as `N(0, σ²)`. -/
theorem equation_S14_noise (proc : GaussianAveragingProcess (P hG) σ Ω) :
    iIndepFun (fun p : ℕ × V => proc.ξ (p.1 + 1) p.2) volume ∧
    ∀ t x, Measure.map (proc.ξ (t + 1) x) volume = gaussianReal 0 (σ ^ 2).toNNReal :=
  ⟨proc.noise_indep, proc.noise_law⟩

/-- A process exists for every noise amplitude. -/
theorem process_exists (σ : ℝ) :
    ∃ (Ω : Type uV) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (volume : Measure Ω)),
      Nonempty (GaussianAveragingProcess (P hG) σ Ω) :=
  exists_gaussianAveragingProcess (P hG) σ

/-- Equation (S15): the lifetime `τ_θ` is the first round `t ≥ 1` at which some
edge difference reaches the threshold `θ`, and `⊤` if no such round occurs. -/
theorem equation_S15 (proc : GaussianAveragingProcess (P hG) σ Ω) (hθ : 0 < θ)
    (T : ℕ) (ω : Ω) :
    lifetime G θ proc ω ≤ T ↔
      ∃ t, 1 ≤ t ∧ t ≤ T ∧
        ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω| :=
  lifetime_le_iff_of_pos proc hθ T ω

/-- Equation (S51): `meanLifetime`, the sum of the survival probabilities
`ℙ(τ_θ > t)`, is the expectation `𝔼[τ_θ]` of the lifetime. -/
theorem equation_S51 (proc : GaussianAveragingProcess (P hG) σ Ω) :
    meanLifetime G θ proc = ∑' t : ℕ, volume {ω | (t : ℕ∞) < lifetime G θ proc ω} ∧
    meanLifetime G θ proc = ∫⁻ ω, (lifetime G θ proc ω : ℝ≥0∞) :=
  ⟨rfl, meanLifetime_eq_lintegral proc θ⟩

/-- The normalized variance `V_t(e)` of equation (S22). -/
abbrev Vt (u v : V) (t : ℕ) : ℝ := normalizedVariance (P hG) u v t

/-- The limiting variance `V_∞(e)` of equation (S28). -/
abbrev Vinf (u v : V) : ℝ := limitingVariance (P hG) u v

/-- Equation (S19): `differenceRow (P hG) u v j z` is entry `z` of the row
`q_eᵀ P^j` for `e = (u, v)`. -/
theorem equation_S19 (u v : V) (j : ℕ) (z : V) :
    differenceRow (P hG) u v j z =
      (kernelMatrix (P hG) ^ j) u z - (kernelMatrix (P hG) ^ j) v z :=
  rfl

/-- **Lemma T2.1** (distribution of an edge difference), equations (S21) and
(S22): `D_t(u, v) = f_t(u) - f_t(v)` has law `N(0, σ² V_t(u, v))`, where
`V_t(u, v) = ∑_{j<t} ‖q_eᵀ P^j‖₂²`. -/
theorem lemma_T2_1 (proc : GaussianAveragingProcess (P hG) σ Ω) (t : ℕ) (u v : V) :
    Measure.map (fun ω => proc.f t u ω - proc.f t v ω) volume =
      gaussianReal 0 (σ ^ 2 * Vt hG u v t).toNNReal ∧
    Vt hG u v t = ∑ j ∈ Finset.range t, ∑ z, differenceRow (P hG) u v j z ^ 2 :=
  ⟨edgeDiff_gaussian proc t u v, rfl⟩

/-- **Lemma T2.2** (sum of squared perturbations needed to reach the
threshold), equation (S25): for `T ≥ 1`, among perturbations `ζ_1, …, ζ_T` for
which the edge difference (S24) has absolute value at least `θ`, the minimum of
`∑_s ‖ζ_s‖₂²` is `θ² / V_T(e)`. -/
theorem lemma_T2_2 {u v : V} (huv : G.Adj u v) {T : ℕ} (hT : 1 ≤ T) (hθ : 0 < θ) :
    IsLeast {E : ℝ | ∃ ζ : ℕ → V → ℝ,
        θ ≤ |∑ s ∈ Finset.Icc 1 T, ∑ z, differenceRow (P hG) u v (T - s) z * ζ s z| ∧
        E = ∑ s ∈ Finset.Icc 1 T, ∑ z, ζ s z ^ 2}
      (θ ^ 2 / Vt hG u v T) :=
  isLeast_perturbation_sum_sq (P hG) huv.ne hT hθ

/-- **Lemma T2.3**, with equation (S28): the series defining `V_∞(u, v)`
converges and `V_t(u, v)` tends to `V_∞(u, v)` from below; on an edge,
`2 ≤ V_∞(e)`. -/
theorem lemma_T2_3 (u v : V) :
    Summable (fun j : ℕ => ∑ z, differenceRow (P hG) u v j z ^ 2) ∧
    Tendsto (Vt hG u v) atTop (𝓝 (Vinf hG u v)) ∧
    (∀ t, Vt hG u v t ≤ Vinf hG u v) ∧
    (G.Adj u v → 2 ≤ Vinf hG u v) :=
  have hs := lazyKernel_variance_summable G (degree_pos hG) hG u v
  ⟨hs, normalizedVariance_tendsto _ u v hs, normalizedVariance_le_limitingVariance _ u v hs,
    fun huv => limitingVariance_ge_two _ huv.ne hs⟩

/-- The effective curvature `κ_eff(e)` of equation (S35). -/
abbrev κeff (u v : V) : ℝ := effectiveCurvature (Vinf hG u v)

omit hG in
/-- Equation (S34) and the definition of effective curvature: for `0 ≤ r < 1`,
the series `2 ∑_j r^(2j)` of the equivalent bond sums to `2 / (1 - r²)`, and an
edge with this limiting variance has effective curvature `1 - r`. -/
theorem equation_S34 {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun j : ℕ => 2 * r ^ (2 * j)) (2 / (1 - r ^ 2)) ∧
    effectiveCurvature (2 / (1 - r ^ 2)) = 1 - r :=
  ⟨by simpa only [pow_mul] using hasSum_two_mul_geometric_sq h0 h1,
    effectiveCurvature_equivalentBond h0⟩

/-- Equation (S35): `κ_eff(e) = 1 - √(1 - 2 / V_∞(e))` and `0 < κ_eff(e) ≤ 1`. -/
theorem equation_S35 {u v : V} (huv : G.Adj u v) :
    κeff hG u v = 1 - Real.sqrt (1 - 2 / Vinf hG u v) ∧
    0 < κeff hG u v ∧ κeff hG u v ≤ 1 :=
  ⟨rfl, effectiveCurvature_pos ((lemma_T2_3 hG u v).2.2.2 huv), effectiveCurvature_le_one _⟩

/-- Equation (S36): `V_∞(e) = 2 / (κ_eff(e) (2 - κ_eff(e)))`. -/
theorem equation_S36 {u v : V} (huv : G.Adj u v) :
    Vinf hG u v = 2 / (κeff hG u v * (2 - κeff hG u v)) :=
  eq_two_div_effectiveCurvature ((lemma_T2_3 hG u v).2.2.2 huv)

/-- The maximum limiting variance `M_G` of equation (S38). -/
abbrev M : ℝ := maxLimitingVariance G (P hG) (edge_exists hG)

/-- The minimum effective curvature `κ_eff^min` of equation (S38). -/
abbrev κeffMin : ℝ := minEffectiveCurvature G (P hG) (edge_exists hG)

/-- Equation (S38): `M_G` is the largest `V_∞(e)` and `κ_eff^min` the smallest
`κ_eff(e)`, and both are attained at the same edge. -/
theorem equation_S38 :
    (∀ u v, G.Adj u v → Vinf hG u v ≤ M hG ∧ κeffMin hG ≤ κeff hG u v) ∧
    ∃ u v, G.Adj u v ∧ Vinf hG u v = M hG ∧ κeff hG u v = κeffMin hG :=
  edge_extrema (edge_exists hG) fun u v _ => (lemma_T2_3 hG u v).1

/-- Equation (S39): `M_G` and `1 / (2 M_G)` in terms of `κ_eff^min`. -/
theorem equation_S39 :
    M hG = 2 / (κeffMin hG * (2 - κeffMin hG)) ∧
    1 / (2 * M hG) = κeffMin hG * (2 - κeffMin hG) / 4 := by
  obtain ⟨u, v, huv, hM, hκ⟩ := (equation_S38 hG).2
  rw [← hM, ← hκ]
  exact ⟨equation_S36 hG huv, one_div_two_mul_eq_effectiveCurvature ((lemma_T2_3 hG u v).2.2.2 huv)⟩

omit hG in
/-- **Lemma T2.4** (two-sided Gaussian tail), equation (S40), for a variable
`Z` with law `N(0, a²)`. -/
theorem lemma_T2_4 {Z : Ω → ℝ} {a : ℝ}
    (hZ : Measure.map Z volume = gaussianReal 0 (a ^ 2).toNNReal) (hθ : 0 < θ) :
    volume.real {ω | θ ≤ |Z ω|} ≤ 2 * Real.exp (-θ ^ 2 / (2 * a ^ 2)) := by
  simpa only [Real.coe_toNNReal _ (sq_nonneg a)] using gaussian_tail_bound hZ hθ

/-- **Theorem 2** (lower bound on the mean lifetime), equations (S46) and
(S47): with `m = |E|` and `Θ = θ/σ`, `𝔼[τ_θ] ≥ exp(Θ² / (2 M_G)) / (4 m)`, the
same bound with the exponent `κ_eff^min (2 - κ_eff^min) Θ² / 4` (equal by
(S39)), and `ℙ(τ_θ ≤ t) ≤ 2 m t exp(-Θ² / (2 M_G))` for every `t`. -/
theorem theorem_2 (proc : GaussianAveragingProcess (P hG) σ Ω) (hθ : 0 < θ) :
    ENNReal.ofReal (Real.exp ((θ / σ) ^ 2 / (2 * M hG)) / (4 * G.edgeFinset.card)) ≤
      meanLifetime G θ proc ∧
    ENNReal.ofReal (Real.exp (κeffMin hG * (2 - κeffMin hG) * (θ / σ) ^ 2 / 4) /
      (4 * G.edgeFinset.card)) ≤ meanLifetime G θ proc ∧
    ∀ t : ℕ, volume {ω | lifetime G θ proc ω ≤ t} ≤
      ENNReal.ofReal (2 * G.edgeFinset.card * t * Real.exp (-(θ / σ) ^ 2 / (2 * M hG))) :=
  have hs := fun u v (_ : G.Adj u v) => (lemma_T2_3 hG u v).1
  ⟨meanLifetime_lower_of_maxLimitingVariance (edge_exists hG) hs proc hθ,
    meanLifetime_lower_of_effectiveCurvature (edge_exists hG) hs proc hθ
      (fun u v huv => ((equation_S38 hG).1 u v huv).2),
    lifetime_probability_le_of_maxLimitingVariance (edge_exists hG) hs proc hθ⟩

/-- Equation (S53) and the bound following it: the bounds of Theorem 2 from a
lower bound `κ₀` on the effective curvature of every edge. -/
theorem equation_S53 (proc : GaussianAveragingProcess (P hG) σ Ω) (hθ : 0 < θ)
    {κ₀ : ℝ} (hfloor : ∀ u v, G.Adj u v → κ₀ ≤ κeff hG u v) :
    ENNReal.ofReal
        (Real.exp (κ₀ * (2 - κ₀) * (θ / σ) ^ 2 / 4) / (4 * G.edgeFinset.card)) ≤
      meanLifetime G θ proc ∧
    ∀ t : ℕ, volume {ω | lifetime G θ proc ω ≤ t} ≤
      ENNReal.ofReal
        (2 * G.edgeFinset.card * t * Real.exp (-κ₀ * (2 - κ₀) * (θ / σ) ^ 2 / 4)) :=
  have hs := fun u v (_ : G.Adj u v) => (lemma_T2_3 hG u v).1
  ⟨meanLifetime_lower_of_effectiveCurvature (edge_exists hG) hs proc hθ hfloor,
    lifetime_probability_le_of_effectiveCurvature (edge_exists hG) hs proc hθ hfloor⟩

/-- **Lemma T2.5** (survival probabilities at fixed time intervals),
equations (S54) and (S55), for `T ≥ 1`, where `blockProbability (Vt hG u v T) (θ / σ)` is
`p_T(e)`. By (S56) the edge difference `D_{n+T}(e)` is the sum of `pastPart`,
from the noise of rounds `1, …, n`, and `freshPart`, from the noise of rounds
`n + 1, …, n + T`. For every real `c`, the probability that
`|c + freshPart| ≥ θ` is at least `p_T(e)`. Moreover
`ℙ(τ_θ > kT) ≤ (1 - p_T(e))^k` for every `k`, and `𝔼[τ_θ] ≤ T / p_T(e)`. -/
theorem lemma_T2_5 (proc : GaussianAveragingProcess (P hG) σ Ω) (hσ : 0 < σ) (hθ : 0 < θ)
    {u v : V} (huv : G.Adj u v) {T : ℕ} (hT : 1 ≤ T) :
    blockProbability (Vt hG u v T) (θ / σ) =
      2 / Real.sqrt (2 * Real.pi * Vt hG u v T) *
        Real.exp (-(θ / σ + 2) ^ 2 / (2 * Vt hG u v T)) ∧
    0 < blockProbability (Vt hG u v T) (θ / σ) ∧
    (∀ (n : ℕ) (ω : Ω), proc.f (n + T) u ω - proc.f (n + T) v ω =
      pastPart proc u v n T ω + freshPart proc u v n T ω) ∧
    (∀ (n : ℕ) (ω : Ω), pastPart proc u v n T ω =
      ∑ s ∈ Finset.Icc 1 n, ∑ z,
        differenceRow (P hG) u v (n + T - s) z * proc.ξ s z ω) ∧
    (∀ (n : ℕ) (ω : Ω), freshPart proc u v n T ω =
      ∑ s ∈ Finset.Icc (n + 1) (n + T), ∑ z,
        differenceRow (P hG) u v (n + T - s) z * proc.ξ s z ω) ∧
    (∀ (n : ℕ) (c : ℝ), ENNReal.ofReal (blockProbability (Vt hG u v T) (θ / σ)) ≤
      volume {ω | θ ≤ |c + freshPart proc u v n T ω|}) ∧
    (∀ k : ℕ, volume {ω | ((k * T : ℕ) : ℕ∞) < lifetime G θ proc ω} ≤
      (1 - ENNReal.ofReal (blockProbability (Vt hG u v T) (θ / σ))) ^ k) ∧
    meanLifetime G θ proc ≤
      T / ENNReal.ofReal (blockProbability (Vt hG u v T) (θ / σ)) :=
  have hV : 0 < Vt hG u v T := normalizedVariance_pos (P hG) huv.ne hT
  ⟨rfl, blockProbability_pos hV _,
    fun n => edgeDiff_eq_past_add_fresh proc u v n T, fun _ _ => rfl, fun _ _ => rfl,
    fun n => abs_add_freshPart_probability proc hσ n hV hθ,
    lifetime_gt_mul_le_pow proc hσ hθ huv hT,
    meanLifetime_upper_bound proc hσ hθ huv hT⟩

/-- The mean lifetime is finite and at least `1` (Section T2.6). -/
theorem mean_lifetime_finite (proc : GaussianAveragingProcess (P hG) σ Ω)
    (hσ : 0 < σ) (hθ : 0 < θ) :
    1 ≤ meanLifetime G θ proc ∧ meanLifetime G θ proc ≠ ⊤ := by
  obtain ⟨d, -⟩ := nonempty_dart (edge_exists hG)
  exact ⟨meanLifetime_ge_one proc hθ, meanLifetime_ne_top proc hσ hθ d.adj⟩

/-- **Theorem 3** (exponential growth rate of the mean lifetime), equation
(S63): `log 𝔼[τ_θ] / Θ² → 1 / (2 M_G) = κ_eff^min (2 - κ_eff^min) / 4` as
`Θ = θ/σ → ∞`, uniformly in the threshold, the noise amplitude, and the
process. -/
theorem theorem_3 :
    1 / (2 * M hG) = κeffMin hG * (2 - κeffMin hG) / 4 ∧
    ∀ ε > 0, ∃ Θ₀ : ℝ,
      ∀ {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] {σ θ : ℝ},
        0 < σ → Θ₀ ≤ θ / σ → ∀ proc : GaussianAveragingProcess (P hG) σ Ω,
          |Real.log (meanLifetime G θ proc).toReal / (θ / σ) ^ 2 - 1 / (2 * M hG)| < ε := by
  refine ⟨(equation_S39 hG).2, fun ε hε => ?_⟩
  obtain ⟨Θ₀, h⟩ := meanLifetime_rate_uniform (edge_exists hG)
    (fun u v _ => (lemma_T2_3 hG u v).1) ε hε
  refine ⟨Θ₀, fun {Ω} _ _ {σ θ} hσ hΘ proc => ?_⟩
  simpa only [mul_div_cancel₀ θ hσ.ne'] using h (θ / σ) hΘ hσ proc

/-- Theorem 3 as a limit along any family of thresholds, noise amplitudes, and
processes with `Θ = θ/σ → ∞`. Such families include `θ → ∞` with `σ` fixed and
`σ ↓ 0` with `θ` fixed. -/
theorem theorem_3_limit {ι : Type*} {l : Filter ι} {σ θ : ι → ℝ}
    (hσ : ∀ i, 0 < σ i) (hΘ : Tendsto (fun i => θ i / σ i) l atTop)
    {Ω : ι → Type uΩ} [∀ i, MeasureSpace (Ω i)]
    [∀ i, IsProbabilityMeasure (volume : Measure (Ω i))]
    (proc : ∀ i, GaussianAveragingProcess (P hG) (σ i) (Ω i)) :
    Tendsto (fun i => Real.log (meanLifetime G (θ i) (proc i)).toReal / (θ i / σ i) ^ 2)
      l (𝓝 (1 / (2 * M hG))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Θ₀, h⟩ := (theorem_3 hG).2 ε hε
  filter_upwards [hΘ.eventually_ge_atTop Θ₀] with i hi
  exact h (hσ i) hi (proc i)

/-! ## Sections T2.7 and T2.8: covariance equation and comparisons -/

/-- Equation (S68): the centring matrix `H = I - (1/n) 𝟙𝟙ᵀ` and `B = HPH`. -/
theorem equation_S68 :
    (centeringMatrix : Matrix V V ℝ) = 1 - Matrix.of (fun _ _ => (Fintype.card V : ℝ)⁻¹) ∧
    centeredKernel (P hG) = centeringMatrix * kernelMatrix (P hG) * centeringMatrix :=
  ⟨rfl, (centeredKernel_mul_centering (P hG)).symm⟩

/-- Equation (S69): the centred values `f̃_t = H f_t` (`centeredValues proc t`)
satisfy `f̃_{t+1} = B f̃_t + H ξ_{t+1}`, and centring leaves the difference
between the values at any two vertices unchanged. -/
theorem equation_S69 (proc : GaussianAveragingProcess (P hG) σ Ω) (t : ℕ) (ω : Ω) :
    (fun x => centeredValues proc t x ω) = centeringMatrix *ᵥ (fun x => proc.f t x ω) ∧
    (fun x => centeredValues proc (t + 1) x ω) =
      centeredKernel (P hG) *ᵥ (fun x => centeredValues proc t x ω) +
        centeringMatrix *ᵥ (fun x => proc.ξ (t + 1) x ω) ∧
    ∀ u v, centeredValues proc t u ω - centeredValues proc t v ω =
      proc.f t u ω - proc.f t v ω :=
  ⟨rfl, centeredValues_update proc t ω, fun u v => centeredValues_difference proc t u v ω⟩

/-- Equation (S70): the normalized covariance `S_t = 𝔼[f̃_t f̃_tᵀ] / σ²` of the
centred values satisfies `S₀ = 0` and `S_{t+1} = B S_t Bᵀ + H`. -/
theorem equation_S70 (proc : GaussianAveragingProcess (P hG) σ Ω) (hσ : 0 < σ) :
    (∀ t x y, (∫ ω, centeredValues proc t x ω * centeredValues proc t y ω) / σ ^ 2 =
      normalizedCovariance (P hG) t x y) ∧
    normalizedCovariance (P hG) 0 = 0 ∧
    ∀ t, normalizedCovariance (P hG) (t + 1) =
      centeredKernel (P hG) * normalizedCovariance (P hG) t * (centeredKernel (P hG))ᵀ +
        centeringMatrix :=
  ⟨centeredValues_normalized_second_moment proc hσ.ne', by simp [normalizedCovariance],
    normalizedCovariance_succ (P hG)⟩

/-- **Proposition T2.6** (covariance equation), equations (S71) and (S72): the
equation `S - B S Bᵀ = H` has a unique solution `S`, `S_t` converges to `S`,
and `V_∞(u, v) = S_uu + S_vv - 2 S_uv` for every pair of vertices. -/
theorem proposition_T2_6 :
    ∃ S : Matrix V V ℝ,
      (∀ S' : Matrix V V ℝ,
        S' - centeredKernel (P hG) * S' * (centeredKernel (P hG))ᵀ = centeringMatrix ↔
          S' = S) ∧
      Tendsto (normalizedCovariance (P hG)) atTop (𝓝 S) ∧
      ∀ u v, Vinf hG u v = S u u + S v v - 2 * S u v := by
  obtain ⟨ℓ, hℓ, hpos⟩ := lazyKernel_exists_positive_power G (degree_pos hG) hG
  have hs := covarianceTerm_summable (P hG) ℓ hℓ hpos
  have hS := covarianceEquation_limitingCovariance (P hG) hs
  exact ⟨limitingCovariance (P hG),
    fun S' => ⟨fun h => covarianceEquation_unique (P hG) ℓ hℓ hpos S' _ h hS, fun h => h ▸ hS⟩,
    normalizedCovariance_tendsto _ hs, fun u v => limitingVariance_eq_covariance _ u v hs⟩

/-- **Proposition T2.7** (a uniform lower bound on discrete Ricci curvature):
if `κ(e) ≥ κ₀ > 0` for every edge, then `κ_eff(e) ≥ κ₀` for every edge. -/
theorem proposition_T2_7 {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hfloor : ∀ u v, G.Adj u v → κ₀ ≤ κ hG u v)
    {u v : V} (huv : G.Adj u v) : κ₀ ≤ κeff hG u v :=
  le_effectiveCurvature_of_le_ricciCurvature hG (P hG) hκ₀ hfloor huv

/-- Equation (S76), for a regular graph of degree `d₀`. The eigenbasis `E` of
`P` given by `regularEigenbasis` is orthonormal, with eigenvalues
`λ_k = E.values k`, eigenvectors `φ_k` the columns of `E.vectors`, and
`c_k = φ_k(u) - φ_k(v)`. The eigenvalues lie in `[0, 1]`, the eigenvectors
with eigenvalue `1` are constant, and with `λ₂` the largest eigenvalue below
`1`, `V_∞(e) = ∑_{λ_k < 1} c_k² / (1 - λ_k²) ≤ 2 / (1 - λ₂²)` and
`κ_eff(e) ≥ 1 - λ₂`. -/
theorem equation_S76 {d₀ : ℕ} (hreg : G.IsRegularOfDegree d₀) {u v : V} (huv : G.Adj u v) :
    let E := regularEigenbasis G (degree_pos hG) hreg
    E.vectors * E.vectorsᵀ = 1 ∧
    kernelMatrix (P hG) * E.vectors = E.vectors * Matrix.diagonal E.values ∧
    (∀ k, E.coefficient u v k = E.vectors u k - E.vectors v k) ∧
    (∀ k, 0 ≤ E.values k ∧ E.values k ≤ 1) ∧
    (∀ k, E.values k = 1 → ∀ x y, E.vectors x k = E.vectors y k) ∧
    (∃ k, E.values k < 1 ∧ E.values k = E.largestEigenvalueBelowOne) ∧
    (∀ k, E.values k < 1 → E.values k ≤ E.largestEigenvalueBelowOne) ∧
    Vinf hG u v = ∑ k with E.values k < 1, E.coefficient u v k ^ 2 / (1 - E.values k ^ 2) ∧
    Vinf hG u v ≤ 2 / (1 - E.largestEigenvalueBelowOne ^ 2) ∧
    1 - E.largestEigenvalueBelowOne ≤ κeff hG u v := by
  intro E
  exact ⟨E.orthogonal, E.eigenvectors, fun _ => rfl,
    regular_eigenvalues_range G _ hreg, regular_eigenvector_one_constant G _ hreg hG,
    regular_largestEigenvalueBelowOne_attained G _ hreg hG,
    E.le_largestEigenvalueBelowOne,
    regular_spectral_variance G _ hreg hG u v,
    regular_spectral_variance_bound G _ hreg hG huv.ne,
    regular_effectiveCurvature_ge_spectralGap G _ hreg hG huv.ne⟩

end Theory

/-! ## Supplementary Methods M1: the family of seven designs

The eight ligand sites are the vertices `(±1, ±1, ±1)` of a cube: the
coordinates of site `v` are the binary digits of `v`, with `coordinate v a`
equal to `false` for `-1` and `true` for `+1`, and `x` least significant. Node
`2a + b` lies on axis `a` on the side of sign `b`: nodes `0, 1` are
`-x, +x`, nodes `2, 3` are `-y, +y`, and nodes `4, 5` are `-z, +z`.
`incident v c` states that site `v` is bonded to node `c`; `endpoints e` are
the two sites joined by the short diagonal `e`, listed in increasing order, and
`hasEndpoint e v` states that `v` is one of them. `![a₀, a₁, …] i` is entry
`i` of the tuple, indexed from `0`. -/

open RhombicFamily

/-- Section M1.1: the parent cell has eight sites and six nodes. A site is
bonded to node `2a + b` when its coordinate `a` has sign `b`, so every site has
three bonds and every node four. The twelve short diagonals are the pairs of
distinct sites with two common nodes. -/
theorem parent_cell :
    Fintype.card Site = 8 ∧ Fintype.card Node = 6 ∧ Fintype.card ShortDiagonal = 12 ∧
    (∀ (v : Site) (a : Fin 3) (b : Bool),
      incident v (Fin.ofNat 6 (2 * a.val + b.toNat)) ↔ coordinate v a = b) ∧
    (∀ v : Site, (Finset.univ.filter (fun c : Node => incident v c)).card = 3) ∧
    (∀ c : Node, (Finset.univ.filter (fun v : Site => incident v c)).card = 4) ∧
    ∀ u v : Site,
      ((∃ e : ShortDiagonal, endpoints e = (min u v, max u v)) ↔
        (Finset.univ.filter (fun c => incident u c ∧ incident v c)).card = 2) :=
  ⟨Fintype.card_fin 8, Fintype.card_fin 6, Fintype.card_fin 12, by decide, by decide, by decide,
    shortDiagonals_iff_common_nodes⟩

/-- Definition 1: a cross-linking pattern is a set of short diagonals in which
no site occurs twice, and a design `(Π, R)` is a cross-linking pattern `Π`
together with a set `R` of deleted nodes. The vertices of its skeleton are the
sites and the nodes outside `R`: a vertex is `⟨.inl v, _⟩` for a site `v` or
`⟨.inr c, hc⟩` for a node `c` with `hc : c ∉ R`. Two sites are adjacent when a
diagonal of `Π` joins them, a site and a node are adjacent when they are bonded
in the parent cell, and two nodes are never adjacent. -/
theorem definition_1 :
    (∀ p : Finset ShortDiagonal,
      IsPattern p ↔ ∀ v : Site, (p.filter (fun e => hasEndpoint e v)).card ≤ 1) ∧
    (∀ d : Design, IsPattern d.pattern) ∧
    (∀ (p : Finset ShortDiagonal) (r : Finset Node), IsPattern p →
      ∃! d : Design, d.pattern = p ∧ d.deleted = r) ∧
    (∀ (d : Design) (u v : Site),
      (skeletonGraph d).Adj ⟨.inl u, trivial⟩ ⟨.inl v, trivial⟩ ↔
        u ≠ v ∧ ∃ e ∈ d.pattern, hasEndpoint e u ∧ hasEndpoint e v) ∧
    (∀ (d : Design) (v : Site) (c : Node) (hc : c ∉ d.deleted),
      (skeletonGraph d).Adj ⟨.inl v, trivial⟩ ⟨.inr c, hc⟩ ↔ incident v c) ∧
    ∀ (d : Design) (c c' : Node) (hc : c ∉ d.deleted) (hc' : c' ∉ d.deleted),
      ¬ (skeletonGraph d).Adj ⟨.inr c, hc⟩ ⟨.inr c', hc'⟩ :=
  ⟨fun _ => Iff.rfl, fun d => d.isPattern,
    fun p r hp => ⟨⟨p, r, hp⟩, ⟨rfl, rfl⟩, by rintro ⟨_, _, _⟩ ⟨rfl, rfl⟩; rfl⟩,
    fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => id⟩

/-- Section M1.1: there are 108 cross-linking patterns (1 empty, 12 with one
diagonal, 42 with two, 44 with three, and 9 with four) and `108 × 64 = 6,912`
designs. -/
theorem design_counts :
    (Finset.univ.filter IsPattern).card = 108 ∧
    (∀ k : Fin 5, (Finset.univ.filter fun p => IsPattern p ∧ p.card = k.val).card =
      ![1, 12, 42, 44, 9] k) ∧
    Fintype.card Design = 6912 :=
  ⟨card_patterns, card_patterns_of_size, card_design⟩

/-- Definition 2: the ligand molecules of a design are the diagonals of its
pattern and the sites that the pattern does not cover. The local environment
of a single site is its number of deleted neighbours; that of a pair is its
number of deleted shared neighbours and its number of deleted exclusive
neighbours. -/
theorem definition_2 (d : Design) :
    (∀ v : Site, Ligand.single v ∈ ligands d ↔ ∀ e ∈ d.pattern, ¬ hasEndpoint e v) ∧
    (∀ e : ShortDiagonal, Ligand.pair e ∈ ligands d ↔ e ∈ d.pattern) ∧
    (∀ v : Site, localEnvironment d (.single v) =
      .single (d.deleted.filter (fun c => incident v c)).card) ∧
    ∀ e : ShortDiagonal, localEnvironment d (.pair e) =
      .pair
        (d.deleted.filter (fun c =>
          incident (endpoints e).1 c ∧ incident (endpoints e).2 c)).card
        (d.deleted.filter (fun c => Xor' (incident (endpoints e).1 c)
          (incident (endpoints e).2 c))).card :=
  ⟨fun _ => mem_ligands d _, fun _ => mem_ligands d _, fun _ => rfl, fun _ => rfl⟩

/-- Definition 3: a design is admissible when (E) all its ligand molecules
have the same local environment and (D) every vertex of its skeleton has
degree at least three. -/
theorem definition_3 (d : Design) :
    (UniformLocalEnvironment d ↔
      ∀ l ∈ ligands d, ∀ m ∈ ligands d, localEnvironment d l = localEnvironment d m) ∧
    (HasMinimumDegreeThree d ↔ ∀ v : SkeletonVertex d, 3 ≤ (skeletonGraph d).degree v) ∧
    (Admissible d ↔ UniformLocalEnvironment d ∧ HasMinimumDegreeThree d) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Section M1.3: of the 6,912 designs, 80 satisfy (E) and 31 are admissible. -/
theorem admissible_counts :
    (Finset.univ.filter UniformLocalEnvironment).card = 80 ∧
    (Finset.univ.filter Admissible).card = 31 :=
  ⟨card_uniform, card_admissible⟩

/-- Section M1.4: the cube has 48 symmetries. The symmetry `s = (i, r)` moves
coordinate `a` to the axis `axisPermutation i a` and reverses the coordinates
in which `r` is `+1`, and every permutation of the three axes occurs. Distinct
symmetries act differently on the sites, and the actions on sites, nodes, and
short diagonals preserve bonding and the ends of the short diagonals. -/
theorem symmetries :
    Fintype.card Symmetry = 48 ∧
    (∀ p : Fin 3 → Fin 3, Function.Bijective p → ∃ i, axisPermutation i = p) ∧
    (∀ (s : Symmetry) (v : Site) (a : Fin 3),
      coordinate (siteAction s v) (axisPermutation s.1 a) =
        Bool.xor (coordinate v a) (coordinate s.2 (axisPermutation s.1 a))) ∧
    Function.Injective siteAction ∧
    (∀ s v c, incident (siteAction s v) (nodeAction s c) ↔ incident v c) ∧
    ∀ s e, endpoints (diagonalAction s e) =
      (min (siteAction s (endpoints e).1) (siteAction s (endpoints e).2),
        max (siteAction s (endpoints e).1) (siteAction s (endpoints e).2)) :=
  ⟨by decide, axisPermutation_complete, coordinate_siteAction, siteAction_injective,
    incident_action, endpoints_action⟩

/-- Section M1.4: a symmetry acts on a design through its pattern and its
deletion set, and two designs are equivalent when a symmetry maps one onto the
other. -/
theorem equivalence (d d' : Design) :
    (∀ s : Symmetry, (transform s d).pattern = d.pattern.image (diagonalAction s) ∧
      (transform s d).deleted = d.deleted.image (nodeAction s)) ∧
    (Equivalent d d' ↔ ∃ s : Symmetry, transform s d = d') :=
  ⟨fun _ => ⟨rfl, rfl⟩, Iff.rfl⟩

/-- Table S3, the two kinds of complete pattern. Parallel: the four diagonals
along `z`. Skew: two diagonals along `x` in the face `z = -1` and two along
`y` in the face `z = +1`. -/
theorem table_S3_patterns (e : ShortDiagonal) :
    (e ∈ parallelPattern ↔ coordinate (endpoints e).1 2 ≠ coordinate (endpoints e).2 2) ∧
    (e ∈ skewPattern ↔
      (coordinate (endpoints e).1 0 ≠ coordinate (endpoints e).2 0 ∧
        coordinate (endpoints e).1 2 = false) ∨
      (coordinate (endpoints e).1 1 ≠ coordinate (endpoints e).2 1 ∧
        coordinate (endpoints e).1 2 = true)) :=
  ⟨mem_parallelPattern e, mem_skewPattern e⟩

/-- Table S3, columns Cross-linking and Deleted nodes, for the rows
`1, 2a, 2b, 3, 4a, 4b, 4c`. -/
theorem table_S3_designs (i : Fin 7) :
    (representative i).pattern =
      ![∅, parallelPattern, skewPattern, parallelPattern, parallelPattern, parallelPattern,
        skewPattern] i ∧
    (representative i).deleted = ![∅, ∅, ∅, {5}, {4, 5}, {0, 1}, {4, 5}] i := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

/-- **Proposition M1.1** (classification): the seven designs of Table S3 are
admissible and pairwise inequivalent, and every admissible design is equivalent
to a unique one of them. -/
theorem proposition_M1_1 :
    (∀ i : Fin 7, Admissible (representative i)) ∧
    (∀ i j : Fin 7, Equivalent (representative i) (representative j) → i = j) ∧
    ∀ d : Design, Admissible d → ∃! i : Fin 7, Equivalent d (representative i) :=
  ⟨representative_admissible, representatives_inequivalent, unique_representative⟩

/-- Table S3, columns Environment, Order, Size, Vertices, and Edges, for the
rows `1, 2a, 2b, 3, 4a, 4b, 4c`. Order is the number of symmetries preserving
the design, and Size is the number of designs equivalent to it. -/
theorem table_S3 (i : Fin 7) :
    (ligands (representative i)).Nonempty ∧
    (∀ l ∈ ligands (representative i), localEnvironment (representative i) l =
      ![.single 0, .pair 0 0, .pair 0 0, .pair 0 1, .pair 0 2, .pair 1 0, .pair 1 0] i) ∧
    (Finset.univ.filter (fun s : Symmetry =>
      transform s (representative i) = representative i)).card = ![48, 16, 8, 8, 16, 8, 8] i ∧
    (Finset.univ.image (fun s : Symmetry => transform s (representative i))).card =
      ![1, 3, 6, 6, 3, 6, 6] i ∧
    Fintype.card (SkeletonVertex (representative i)) = ![14, 14, 14, 13, 12, 12, 12] i ∧
    (skeletonGraph (representative i)).edgeFinset.card = ![24, 28, 28, 24, 20, 20, 20] i :=
  ⟨(representative_environments i).1, (representative_environments i).2,
    representative_stabilizer_orders i, representative_class_sizes i,
    representative_skeleton_counts i⟩

/-- **Lemma M1.2** (consequences): every admissible design has at most two
deleted nodes, a connected skeleton, and ligand molecules that are all
equivalent under the symmetries preserving the design. A symmetry `s` maps a
single site by `siteAction s` and a pair by `diagonalAction s`
(`ligandAction s`). -/
theorem lemma_M1_2 (d : Design) (h : Admissible d) :
    d.deleted.card ≤ 2 ∧ (skeletonGraph d).Connected ∧
    ∀ l ∈ ligands d, ∀ m ∈ ligands d,
      ∃ s : Symmetry, transform s d = d ∧ ligandAction s l = m :=
  admissible_consequences d h

end Paper
