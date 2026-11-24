import GraphStability.TransportDuality
import GraphStability.VarianceLimit
import GraphStability.EffectiveCurvature

/-!
# A lower bound from discrete Ricci curvature (Proposition T2.7)

On a finite connected graph on which the transport distance across every edge
is at most `r ≥ 0`, the function `P^j g` is `r^j`-Lipschitz for every
1-Lipschitz `g`. Testing a row `q_eᵀ P^j` against the indicator of its positive
entries bounds the sum of those entries, and the squared Euclidean norm of a
row with sum zero is at most twice the square of the sum of its positive
entries. If every edge has discrete Ricci curvature at least `κ₀ > 0`, set
`r = 1 - κ₀`. For each edge `e`, the squared norm of the row `q_eᵀ P^j` is at
most `2 (r²)^j`. Summing gives limiting variance at most
`2/(κ₀(2 - κ₀))` and hence effective curvature at least `κ₀` on that edge.
-/

noncomputable section

open scoped Matrix

namespace GraphStability

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

omit [DecidableEq V] in
/-- On a connected graph with `W₁(P x, P y) ≤ r` on every edge, if
`|g x - g y| ≤ L d(x, y)` for all `x`, `y` with `L ≥ 0`, then
`|(Pg)(x) - (Pg)(y)| ≤ r L d(x, y)` for all `x`, `y`. -/
theorem markovOperator_contracts (hG : G.Connected) (P : MarkovKernel V)
    {r L : ℝ} (hL : 0 ≤ L)
    (htransport : ∀ x y, G.Adj x y → wasserstein1 G (P x) (P y) ≤ r)
    (g : V → ℝ) (hg : ∀ x y, |g x - g y| ≤ L * graphDistance G x y) (x y : V) :
    |markovOperator P g x - markovOperator P g y| ≤ r * L * graphDistance G x y := by
  apply abs_sub_le_mul_dist_of_adj hG _ _
  intro a b hab
  obtain ⟨π, hfst, hsnd, hcost⟩ := exists_optimal_transportPlan G (P a) (P b)
  have hpair : markovOperator P g a - markovOperator P g b =
      ∑ p : V × V, (g p.1 - g p.2) * (π p).toReal := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [sum_transportPlan_fst π hfst g, sum_transportPlan_snd π hsnd g]
    simp only [markovOperator, mul_comm]
  calc
    |markovOperator P g a - markovOperator P g b| =
        |∑ p : V × V, (g p.1 - g p.2) * (π p).toReal| := congrArg abs hpair
    _ ≤ ∑ p : V × V, |(g p.1 - g p.2) * (π p).toReal| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : V × V, L * graphDistance G p.1 p.2 * (π p).toReal := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_right (hg p.1 p.2) ENNReal.toReal_nonneg
    _ = L * wasserstein1 G (P a) (P b) := by
      simp only [hcost, Finset.mul_sum, mul_assoc]
    _ ≤ L * r := mul_le_mul_of_nonneg_left (htransport a b hab) hL
    _ = r * L := mul_comm _ _

/-- On a connected graph, if `r ≥ 0`, `W₁(P x, P y) ≤ r` on every edge, and `g`
is 1-Lipschitz, then `|(P^j g)(x) - (P^j g)(y)| ≤ r^j d(x, y)`. -/
theorem pow_mulVec_increment_bound (hG : G.Connected) (P : MarkovKernel V)
    {r : ℝ} (hr : 0 ≤ r)
    (htransport : ∀ x y, G.Adj x y → wasserstein1 G (P x) (P y) ≤ r)
    (g : V → ℝ) (hg : IsOneLipschitz G g) (j : ℕ) (x y : V) :
    |((kernelMatrix P ^ j) *ᵥ g) x - ((kernelMatrix P ^ j) *ᵥ g) y| ≤
      r ^ j * graphDistance G x y := by
  induction j generalizing x y with
  | zero => simpa only [pow_zero, Matrix.one_mulVec, one_mul] using hg x y
  | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
      exact markovOperator_contracts hG P (pow_nonneg hr j) htransport _ ih x y

/-- Pairing `differenceRow P u v j` with `g` gives `(P^j g)(u) - (P^j g)(v)`. -/
theorem differenceRow_pairing (P : MarkovKernel V) (u v : V) (j : ℕ) (g : V → ℝ) :
    (∑ z, differenceRow P u v j z * g z) =
      ((kernelMatrix P ^ j) *ᵥ g) u - ((kernelMatrix P ^ j) *ᵥ g) v := by
  simp only [differenceRow, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- The sum of the positive entries of a row vector `w`. -/
def positiveMass (w : V → ℝ) : ℝ := ∑ z, max (w z) 0

/-- The indicator function of the positive entries of a row vector `w`. -/
def positiveIndicator (w : V → ℝ) (z : V) : ℝ := if 0 < w z then 1 else 0

omit [DecidableEq V] in
/-- Pairing `w` with `positiveIndicator w` yields `positiveMass w`. -/
theorem pairing_positiveIndicator (w : V → ℝ) :
    (∑ z, w z * positiveIndicator w z) = positiveMass w := by
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : 0 < w z
  · simp [positiveIndicator, hz, max_eq_left hz.le]
  · simp [positiveIndicator, hz, max_eq_right (le_of_not_gt hz)]

omit [Fintype V] [DecidableEq V] in
/-- On a connected graph, the indicator of the positive entries of `w` is
1-Lipschitz. -/
theorem positiveIndicator_isOneLipschitz (hG : G.Connected) (w : V → ℝ) :
    IsOneLipschitz G (positiveIndicator w) := by
  intro x y
  have hedge (a b : V) (_hab : G.Adj a b) :
      |positiveIndicator w a - positiveIndicator w b| ≤ 1 := by
    unfold positiveIndicator
    split_ifs <;> norm_num
  simpa only [one_mul] using abs_sub_le_mul_dist_of_adj hG _ 1 hedge x y

omit [DecidableEq V] in
/-- A row whose entries sum to zero has squared Euclidean norm at most
`2 * positiveMass w ^ 2`. -/
theorem sqNorm_le_two_mul_positiveMass_sq (w : V → ℝ) (hw : ∑ z, w z = 0) :
    (∑ z, w z ^ 2) ≤ 2 * positiveMass w ^ 2 := by
  have hmass : (∑ z, max (w z) 0) = ∑ z, max (-w z) 0 := by
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    simpa only [max_zero_sub_max_neg_zero_eq_self] using hw
  have hsq (z : V) : w z ^ 2 = max (w z) 0 ^ 2 + max (-w z) 0 ^ 2 := by
    rcases le_total 0 (w z) with hz | hz
    · simp [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    · simp [max_eq_right hz, max_eq_left (neg_nonneg.mpr hz)]
  calc
    (∑ z, w z ^ 2) = (∑ z, max (w z) 0 ^ 2) + ∑ z, max (-w z) 0 ^ 2 := by
      simp_rw [hsq, Finset.sum_add_distrib]
    _ ≤ (∑ z, max (w z) 0) ^ 2 + (∑ z, max (-w z) 0) ^ 2 :=
      add_le_add
        (Finset.sum_sq_le_sq_sum_of_nonneg (fun z _ => le_max_right (w z) 0))
        (Finset.sum_sq_le_sq_sum_of_nonneg (fun z _ => le_max_right (-w z) 0))
    _ = 2 * positiveMass w ^ 2 := by rw [← hmass, positiveMass, two_mul]

/-- On a connected graph, if `r ≥ 0` and `W₁(P x, P y) ≤ r` on every edge, then
`positiveMass (differenceRow P u v j) ≤ r^j` for every edge `(u, v)`. -/
theorem differenceRow_positiveMass_le (hG : G.Connected) (P : MarkovKernel V)
    {r : ℝ} (hr : 0 ≤ r)
    (htransport : ∀ x y, G.Adj x y → wasserstein1 G (P x) (P y) ≤ r)
    (j : ℕ) {u v : V} (huv : G.Adj u v) :
    positiveMass (differenceRow P u v j) ≤ r ^ j := by
  have hbound := pow_mulVec_increment_bound hG P hr htransport _
    (positiveIndicator_isOneLipschitz hG (differenceRow P u v j)) j u v
  have hdist : graphDistance G u v = 1 := by
    simp [graphDistance, SimpleGraph.dist_eq_one_iff_adj.mpr huv]
  rw [hdist, mul_one] at hbound
  rw [← pairing_positiveIndicator, differenceRow_pairing]
  exact (le_abs_self _).trans hbound

/-- On a connected graph, if `r ≥ 0` and `W₁(P x, P y) ≤ r` on every edge, then
`‖differenceRow P u v j‖₂² ≤ 2 (r²)^j` for every edge `(u, v)` and every `j`. -/
theorem differenceRow_sqNorm_le_geometric (hG : G.Connected) (P : MarkovKernel V)
    {r : ℝ} (hr : 0 ≤ r)
    (htransport : ∀ x y, G.Adj x y → wasserstein1 G (P x) (P y) ≤ r)
    (j : ℕ) {u v : V} (huv : G.Adj u v) :
    (∑ z, differenceRow P u v j z ^ 2) ≤ 2 * (r ^ 2) ^ j := by
  calc
    (∑ z, differenceRow P u v j z ^ 2) ≤ 2 * positiveMass (differenceRow P u v j) ^ 2 :=
      sqNorm_le_two_mul_positiveMass_sq _ (differenceRow_row_sum P u v j)
    _ ≤ 2 * (r ^ j) ^ 2 := by
      gcongr
      · exact Finset.sum_nonneg fun z _ => le_max_right _ 0
      · exact differenceRow_positiveMass_le hG P hr htransport j huv
    _ = 2 * (r ^ 2) ^ j := by rw [pow_right_comm r j 2]

/-- On a connected graph, if `W₁(P x, P y) ≤ r` on every edge with
`0 ≤ r < 1`, then for every edge `(u, v)` the series defining `V_∞(u, v)`
converges and `V_∞(u, v) ≤ 2 / (1 - r²)`. -/
theorem limitingVariance_le_of_edge_contraction (hG : G.Connected) (P : MarkovKernel V)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (htransport : ∀ x y, G.Adj x y → wasserstein1 G (P x) (P y) ≤ r)
    {u v : V} (huv : G.Adj u v) :
    Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2) ∧
      limitingVariance P u v ≤ 2 / (1 - r ^ 2) := by
  have hgeo := hasSum_two_mul_geometric_sq hr hr1
  have hle := fun j => differenceRow_sqNorm_le_geometric hG P hr htransport j huv
  have hs := Summable.of_nonneg_of_le
    (fun j => Finset.sum_nonneg fun z _ => sq_nonneg (differenceRow P u v j z)) hle hgeo.summable
  exact ⟨hs, (hs.tsum_le_tsum hle hgeo.summable).trans_eq hgeo.tsum_eq⟩

/-- Proposition T2.7: on a connected graph, if `κ(e) ≥ κ₀ > 0` for every edge
`e`, then `κ_eff(e) ≥ κ₀` for every edge `e`. -/
theorem le_effectiveCurvature_of_le_ricciCurvature (hG : G.Connected) (P : MarkovKernel V)
    {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hcurvature : ∀ x y, G.Adj x y → κ₀ ≤ ricciCurvature G P x y)
    {u v : V} (huv : G.Adj u v) :
    κ₀ ≤ effectiveCurvature (limitingVariance P u v) := by
  have htransport : ∀ x y, G.Adj x y → wasserstein1 G (P x) (P y) ≤ 1 - κ₀ := by
    intro x y hxy
    linarith [hcurvature x y hxy, ricciCurvature_eq_one_sub_wasserstein_of_adj (P := P) hxy]
  have hr : 0 ≤ 1 - κ₀ :=
    (wasserstein1_nonneg (G := G) (P u) (P v)).trans (htransport u v huv)
  obtain ⟨hs, hle⟩ := limitingVariance_le_of_edge_contraction hG P hr
    (sub_lt_self 1 hκ₀) htransport huv
  have h2 := limitingVariance_ge_two P huv.ne hs
  simpa only [effectiveCurvature_equivalentBond hr, sub_sub_cancel] using
    effectiveCurvature_antitoneOn h2 (h2.trans hle) hle

end GraphStability
