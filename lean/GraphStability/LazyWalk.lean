import GraphStability.Transport

/-!
# The averaging rule (equation (S2))
-/

noncomputable section

namespace GraphStability

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The entries of the averaging rule: `1/2` on the diagonal and
`1/(2 deg x)` for each neighbour. -/
def lazyMass (x y : V) : ℝ :=
  if y = x then 1 / 2
  else if G.Adj x y then 1 / (2 * (G.degree x : ℝ)) else 0

/-- Every entry of `lazyMass G` is non-negative. -/
theorem lazyMass_nonneg (x y : V) : 0 ≤ lazyMass G x y := by
  unfold lazyMass
  split_ifs <;> positivity

/-- `lazyMass G x y` is the sum of a stay part, `1/2` when `y = x`, and a jump
part, `1 / (2 deg x)` when `y` is a neighbour of `x`. -/
theorem lazyMass_split (x y : V) :
    lazyMass G x y = (if y = x then (1 : ℝ) / 2 else 0)
      + (if G.Adj x y then 1 / (2 * (G.degree x : ℝ)) else 0) := by
  by_cases h : y = x <;> simp [lazyMass, h]

/-- Each row of `lazyMass G` sums to `1` when the vertex has positive degree. -/
theorem lazyMass_sum (x : V) (hd : 0 < G.degree x) : ∑ y, lazyMass G x y = 1 := by
  simp only [lazyMass_split, Finset.sum_add_distrib, Fintype.sum_ite_eq']
  rw [← Finset.sum_filter, Finset.sum_const, ← SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have hdeg : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  norm_num

/-- The averaging rule: the 1/2-lazy random walk on a graph without isolated
vertices. -/
def lazyKernel (hd : ∀ x : V, 0 < G.degree x) : MarkovKernel V := fun x =>
  FiniteTransport.pmfOfSimplex (lazyMass G x) ⟨lazyMass_nonneg G x, lazyMass_sum G x (hd x)⟩

/-- Equation (S2): the entries of the averaging rule, as real numbers. -/
theorem lazyKernel_toReal (hd : ∀ x : V, 0 < G.degree x) (x y : V) :
    ((lazyKernel G hd x) y).toReal = lazyMass G x y :=
  FiniteTransport.pmfOfSimplex_toReal _ _ y

end GraphStability
