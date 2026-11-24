import GraphStability.VarianceLimit
import GraphStability.EffectiveCurvature

/-!
# Extrema over the edges (equation (S38))
-/

noncomputable section

namespace GraphStability

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {P : MarkovKernel V}

omit [DecidableEq V] in
/-- A graph with an edge has an oriented edge. -/
theorem nonempty_dart (hE : G.edgeFinset.Nonempty) :
    (Finset.univ : Finset G.Dart).Nonempty := by
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v => exact ⟨⟨(u, v), SimpleGraph.mem_edgeFinset.mp he⟩, Finset.mem_univ _⟩

/-- The maximum limiting variance `M_G` over all edges of `G`. -/
def maxLimitingVariance (G : SimpleGraph V) [DecidableRel G.Adj] (P : MarkovKernel V)
    (hE : G.edgeFinset.Nonempty) : ℝ :=
  (Finset.univ : Finset G.Dart).sup' (nonempty_dart hE)
    fun d => limitingVariance P d.fst d.snd

/-- The limiting variance of every edge is at most the maximum. -/
theorem limitingVariance_le_max (hE : G.edgeFinset.Nonempty)
    {u v : V} (hadj : G.Adj u v) :
    limitingVariance P u v ≤ maxLimitingVariance G P hE :=
  Finset.le_sup' (fun d : G.Dart => limitingVariance P d.fst d.snd)
    (Finset.mem_univ (⟨(u, v), hadj⟩ : G.Dart))

/-- Some edge of `G` attains `maxLimitingVariance G P hE`. -/
theorem exists_edge_maxLimitingVariance (hE : G.edgeFinset.Nonempty) :
    ∃ u v, G.Adj u v ∧ limitingVariance P u v = maxLimitingVariance G P hE := by
  obtain ⟨d, -, hmax⟩ := Finset.exists_mem_eq_sup' (nonempty_dart hE)
    fun d : G.Dart => limitingVariance P d.fst d.snd
  exact ⟨d.fst, d.snd, d.adj, hmax.symm⟩

/-- The minimum effective curvature `κ_eff^min` over all edges of `G`. -/
def minEffectiveCurvature (G : SimpleGraph V) [DecidableRel G.Adj] (P : MarkovKernel V)
    (hE : G.edgeFinset.Nonempty) : ℝ :=
  (Finset.univ : Finset G.Dart).inf' (nonempty_dart hE)
    fun d => effectiveCurvature (limitingVariance P d.fst d.snd)

/-- Equation (S38): if the series defining `V_∞(e)` converges on every edge, one
edge attains both the maximum limiting variance and the minimum effective
curvature. -/
theorem edge_extrema (hE : G.edgeFinset.Nonempty)
    (hs : ∀ u v, G.Adj u v → Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) :
    (∀ u v, G.Adj u v → limitingVariance P u v ≤ maxLimitingVariance G P hE ∧
      minEffectiveCurvature G P hE ≤ effectiveCurvature (limitingVariance P u v)) ∧
    ∃ u v, G.Adj u v ∧ limitingVariance P u v = maxLimitingVariance G P hE ∧
      effectiveCurvature (limitingVariance P u v) = minEffectiveCurvature G P hE := by
  have hmin (d : G.Dart) : minEffectiveCurvature G P hE ≤
      effectiveCurvature (limitingVariance P d.fst d.snd) :=
    Finset.inf'_le (fun e : G.Dart => effectiveCurvature (limitingVariance P e.fst e.snd))
      (Finset.mem_univ d)
  obtain ⟨u, v, huv, hmax⟩ := exists_edge_maxLimitingVariance (P := P) hE
  refine ⟨fun x y hxy => ⟨limitingVariance_le_max hE hxy, hmin ⟨(x, y), hxy⟩⟩,
    u, v, huv, hmax, le_antisymm ?_ (hmin ⟨(u, v), huv⟩)⟩
  refine Finset.le_inf' _ _ fun d _ => ?_
  have hle := (limitingVariance_le_max (P := P) hE d.adj).trans_eq hmax.symm
  have h2 := limitingVariance_ge_two P d.adj.ne (hs _ _ d.adj)
  exact effectiveCurvature_antitoneOn h2 (h2.trans hle) hle

end GraphStability
