import GraphStability.GaussianTail
import GraphStability.Lifetime

/-!
# Lower bound on the mean lifetime (Theorem 2)

A bound `B` on the normalized variances `V_t(e)` gives a Gaussian tail bound
for each edge and each round. Summing over all edges (each counted once) and
over rounds `1, …, T` bounds the probability of a break by round `T`; summing
the survival probabilities yields `𝔼[τ_θ] ≥ exp(Θ² / (2 B)) / (4 |E|)` with
`Θ = θ/σ`.
-/

noncomputable section

open MeasureTheory

namespace GraphStability

variable {V Ω : Type*}

/-- For an unordered pair of vertices, the event that the absolute difference
of their values is at least `θ`. -/
def edgeThresholdEvent (f : V → Ω → ℝ) (θ : ℝ) : Sym2 V → Set Ω :=
  Sym2.lift ⟨fun u v => {ω | θ ≤ |f u ω - f v ω|}, fun u v => by simp only [abs_sub_comm]⟩

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The event that some edge breaks is a union indexed by unoriented edges. -/
theorem breakEvent_eq_edgeUnion (f : V → Ω → ℝ) (θ : ℝ) :
    {ω | ∃ u v, G.Adj u v ∧ θ ≤ |f u ω - f v ω|} =
      ⋃ e ∈ G.edgeFinset, edgeThresholdEvent f θ e := by
  ext ω
  constructor
  · rintro ⟨u, v, huv, hθ⟩
    exact Set.mem_biUnion (by simpa using huv : s(u, v) ∈ G.edgeFinset) hθ
  · intro hω
    rcases Set.mem_iUnion₂.mp hω with ⟨e, he, hω⟩
    induction e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, by simpa using he, hω⟩

/-- The coefficient `A_Θ = 2 |E| exp(-Θ² / (2 B))` of equation (S50), with a
general variance bound `B` in place of `M_G`. -/
def edgeUnionBound (G : SimpleGraph V) [DecidableRel G.Adj] (B Θ : ℝ) : ℝ :=
  2 * G.edgeFinset.card * Real.exp (-Θ ^ 2 / (2 * B))

variable [DecidableEq V]
  [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
  {P : MarkovKernel V} {σ : ℝ}

/-- Equation (S49): if `0 < V_t(u, v) ≤ B` and `θ > 0`, then
`ℙ(|f_t(u) - f_t(v)| ≥ θ) ≤ 2 exp(-θ² / (2 σ² B))`. -/
theorem edgeDiff_measure_le (proc : GaussianAveragingProcess P σ Ω)
    {θ B : ℝ} (hθ : 0 < θ) {t : ℕ} {u v : V}
    (hV0 : 0 < normalizedVariance P u v t) (hV : normalizedVariance P u v t ≤ B) :
    volume {ω | θ ≤ |proc.f t u ω - proc.f t v ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-θ ^ 2 / (2 * (σ ^ 2 * B)))) := by
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr ?_
  rw [← measureReal_def]
  have htail := gaussian_tail_bound (edgeDiff_gaussian proc t u v) hθ
  rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hV0.le)] at htail
  have hmono : -θ ^ 2 / (2 * (σ ^ 2 * normalizedVariance P u v t)) ≤
      -θ ^ 2 / (2 * (σ ^ 2 * B)) := by
    have h := div_le_div_of_nonneg_left (sq_nonneg θ) hV0 hV
    simpa only [neg_div, div_div, mul_assoc, mul_left_comm, mul_comm] using
      div_le_div_of_nonneg_right (neg_le_neg h) (show 0 ≤ 2 * σ ^ 2 by positivity)
  linarith [Real.exp_le_exp.mpr hmono]

/-- For `θ > 0` and `t ≥ 1`, if `V_t(e) ≤ B` for every edge `e`, the
probability that some absolute edge difference is at least `θ` at round `t` is
at most `edgeUnionBound G B (θ / σ)`. -/
theorem break_probability_le_edgeUnionBound
    (proc : GaussianAveragingProcess P σ Ω)
    {θ B : ℝ} (hθ : 0 < θ) {t : ℕ} (ht : 1 ≤ t)
    (hB : ∀ u v, G.Adj u v → normalizedVariance P u v t ≤ B) :
    volume {ω | ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω|}
      ≤ ENNReal.ofReal (edgeUnionBound G B (θ / σ)) := by
  rw [breakEvent_eq_edgeUnion]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hexp : -θ ^ 2 / (2 * (σ ^ 2 * B)) = -(θ / σ) ^ 2 / (2 * B) := by
    rw [div_pow, neg_div, neg_div, div_div]
    congr 2
    ring
  have htail : ∀ e ∈ G.edgeFinset, volume (edgeThresholdEvent (proc.f t) θ e)
      ≤ ENNReal.ofReal (2 * Real.exp (-(θ / σ) ^ 2 / (2 * B))) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have hadj : G.Adj u v := by simpa using he
      rw [← hexp]
      exact edgeDiff_measure_le proc hθ (normalizedVariance_pos P hadj.ne ht) (hB u v hadj)
  refine (Finset.sum_le_sum htail).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by unfold edgeUnionBound; ring))

/-- Equation (S47): if `θ > 0` and `V_T(e) ≤ B` for every edge `e`, then
`ℙ(τ_θ ≤ T) ≤ 2 |E| T exp(-Θ² / (2 B))` with `Θ = θ/σ`. -/
theorem lifetime_probability_le
    (proc : GaussianAveragingProcess P σ Ω)
    {θ B : ℝ} (hθ : 0 < θ) (T : ℕ)
    (hB : ∀ u v, G.Adj u v → normalizedVariance P u v T ≤ B) :
    volume {ω | lifetime G θ proc ω ≤ T} ≤
      ENNReal.ofReal (2 * G.edgeFinset.card * T * Real.exp (-(θ / σ) ^ 2 / (2 * B))) := by
  rw [show 2 * (G.edgeFinset.card : ℝ) * T * Real.exp (-(θ / σ) ^ 2 / (2 * B)) =
    (T : ℝ) * edgeUnionBound G B (θ / σ) by unfold edgeUnionBound; ring,
    lifetime_le_eq_union_of_pos proc hθ]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hper : ∀ t ∈ Finset.Icc 1 T,
      volume {ω | ∃ u v, G.Adj u v ∧ θ ≤ |proc.f t u ω - proc.f t v ω|}
        ≤ ENNReal.ofReal (edgeUnionBound G B (θ / σ)) := by
    intro t ht
    exact break_probability_le_edgeUnionBound proc hθ (Finset.mem_Icc.mp ht).1 fun u v huv =>
      (normalizedVariance_mono P u v (Finset.mem_Icc.mp ht).2).trans (hB u v huv)
  refine (Finset.sum_le_sum hper).trans ?_
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-- The sum of `1 - q t` over `t < N`, in closed form. -/
private theorem sum_affine_survival (q : ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range N, (1 - q * (t : ℝ)) =
      N - q * N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- For `q > 0`, the sum of `1 - q t` over `t < ⌈1/q⌉` is at least `1/(2q)`. -/
private theorem half_reciprocal_le_affine_sum {q : ℝ} (hq : 0 < q) :
    1 / (2 * q) ≤ ∑ t ∈ Finset.range ⌈1 / q⌉₊, (1 - q * (t : ℝ)) := by
  let N := ⌈1 / q⌉₊
  have hNlo : 1 / q ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) < 1 / q + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlast : ((N : ℝ) - 1) * q ≤ 1 := (le_div_iff₀ hq).mp (by linarith)
  rw [sum_affine_survival]
  calc
    1 / (2 * q) = (1 / q) / 2 := by ring
    _ ≤ (N : ℝ) / 2 := by linarith
    _ ≤ (N : ℝ) - q * N * (N - 1) / 2 := by
      nlinarith only [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.mpr hlast)]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- If `q > 0` and `ℙ(τ_θ ≤ t) ≤ q t` for every round `t`, then
`𝔼[τ_θ] ≥ 1 / (2 q)`. -/
theorem meanLifetime_ge_half_reciprocal
    (proc : GaussianAveragingProcess P σ Ω)
    (θ : ℝ) {q : ℝ} (hq : 0 < q)
    (hbreak : ∀ t : ℕ, volume {ω | lifetime G θ proc ω ≤ t}
      ≤ ENNReal.ofReal (q * t)) :
    ENNReal.ofReal (1 / (2 * q)) ≤ meanLifetime G θ proc := by
  let N := ⌈1 / q⌉₊
  have hsurvival : ∀ t : ℕ, 1 - q * t ≤
      (volume {ω | t < lifetime G θ proc ω}).toReal := by
    intro t
    have hcompl := measureReal_add_measureReal_compl (μ := volume)
      (measurableSet_lifetime_gt (G := G) proc θ t)
    have hprob : (volume {ω | lifetime G θ proc ω ≤ t}).toReal ≤ q * t :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hbreak t)
    simp only [measureReal_def, Set.compl_setOf, not_lt, measure_univ,
      ENNReal.toReal_one] at hcompl
    linarith
  have hsum : (1 / (2 * q)) ≤
      (∑ t ∈ Finset.range N, volume {ω | t < lifetime G θ proc ω}).toReal := by
    rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
    exact (half_reciprocal_le_affine_sum hq).trans (Finset.sum_le_sum fun t _ => hsurvival t)
  exact ((ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.sum_ne_top.mpr fun _ _ => measure_ne_top _ _)).mpr hsum).trans
    (ENNReal.sum_le_tsum (Finset.range N))

/-- Equation (S46): for `θ > 0` on a graph with an edge, if `V_t(e) ≤ B` for
every edge `e` and every round `t`, then
`𝔼[τ_θ] ≥ exp(Θ² / (2 B)) / (4 |E|)` with `Θ = θ/σ`. -/
theorem meanLifetime_lower_bound
    (proc : GaussianAveragingProcess P σ Ω)
    {θ B : ℝ} (hθ : 0 < θ)
    (hE : G.edgeFinset.Nonempty)
    (hB : ∀ t u v, G.Adj u v → normalizedVariance P u v t ≤ B) :
    ENNReal.ofReal (Real.exp ((θ / σ) ^ 2 / (2 * B)) /
      (4 * (G.edgeFinset.card : ℝ))) ≤ meanLifetime G θ proc := by
  have hq : 0 < edgeUnionBound G B (θ / σ) := by
    have : (0 : ℝ) < G.edgeFinset.card := Nat.cast_pos.mpr hE.card_pos
    unfold edgeUnionBound
    positivity
  have hmean := meanLifetime_ge_half_reciprocal proc θ hq fun t => by
    simpa only [edgeUnionBound, mul_assoc, mul_left_comm, mul_comm] using
      lifetime_probability_le proc hθ t (hB t)
  have hrewrite : 1 / (2 * edgeUnionBound G B (θ / σ)) =
      Real.exp ((θ / σ) ^ 2 / (2 * B)) / (4 * (G.edgeFinset.card : ℝ)) := by
    unfold edgeUnionBound
    rw [neg_div, Real.exp_neg]
    field_simp
    ring
  rwa [hrewrite] at hmean

end GraphStability
