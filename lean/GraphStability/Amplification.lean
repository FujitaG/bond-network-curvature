import GraphStability.TransportDuality

/-!
# Negative discrete Ricci curvature and amplification (Theorem 1)
-/

namespace GraphStability

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V}

/-- Theorem 1, equation (S13): on an edge `e = (u, v)` of a connected graph, the
maximum of `|(Pg)(u) - (Pg)(v)|` over all 1-Lipschitz functions `g` is `1 - κ(e)`. -/
theorem isGreatest_edge_amplification (hG : G.Connected) {P : MarkovKernel V}
    {u v : V} (huv : G.Adj u v) :
    IsGreatest {a : ℝ | ∃ g : V → ℝ, IsOneLipschitz G g ∧
      a = |markovOperator P g u - markovOperator P g v|}
      (1 - ricciCurvature G P u v) := by
  rw [ricciCurvature_eq_one_sub_wasserstein_of_adj huv, sub_sub_cancel]
  simpa only [markovOperator, mul_sub, Finset.sum_sub_distrib, mul_comm] using
    isGreatest_abs_pairing hG (P u) (P v)

/-- Theorem 1: an edge `(u, v)` of a connected graph has negative discrete Ricci
curvature if and only if it admits an amplification mode, that is, a 1-Lipschitz
function `g` with `|(Pg)(u) - (Pg)(v)| > 1`. -/
theorem negative_curvature_iff_edge_amplification (hG : G.Connected)
    {P : MarkovKernel V} {u v : V} (huv : G.Adj u v) :
    ricciCurvature G P u v < 0 ↔
      ∃ g : V → ℝ, IsOneLipschitz G g ∧
        1 < |markovOperator P g u - markovOperator P g v| := by
  have hmaximum := isGreatest_edge_amplification (P := P) hG huv
  have hiff : ricciCurvature G P u v < 0 ↔ 1 < 1 - ricciCurvature G P u v := by
    rw [lt_sub_iff_add_lt, add_lt_iff_neg_left]
  rw [hiff, lt_isLUB_iff hmaximum.isLUB]
  exact ⟨fun ⟨_, ⟨g, hg, rfl⟩, h⟩ => ⟨g, hg, h⟩, fun ⟨g, hg, h⟩ => ⟨_, ⟨g, hg, rfl⟩, h⟩⟩

end GraphStability
