import GraphStability.Variance
import GraphStability.LazyWalk

/-!
# The limiting variance is finite (Lemma T2.3)

Some power of the averaging matrix of a finite connected graph has strictly
positive entries, so multiplication by it contracts the sum of absolute values
of every row whose entries sum to zero. The squared norms of the rows
`q_eᵀ P^j` are then bounded by a geometric series.
-/

noncomputable section

namespace GraphStability

open Finset Filter Matrix
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The limiting variance `V_∞(u, v) = ∑_j ‖q_eᵀ P^j‖₂²` of equation (S28),
as an infinite sum. -/
def limitingVariance (P : MarkovKernel V) (u v : V) : ℝ :=
  ∑' j : ℕ, ∑ z, differenceRow P u v j z ^ 2

/-- If the series converges, `V_t` tends to the limiting variance. -/
theorem normalizedVariance_tendsto (P : MarkovKernel V) (u v : V)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) :
    Tendsto (normalizedVariance P u v) atTop (𝓝 (limitingVariance P u v)) :=
  hs.hasSum.tendsto_sum_nat

/-- If the series converges, `V_t` is at most the limiting variance. -/
theorem normalizedVariance_le_limitingVariance (P : MarkovKernel V) (u v : V)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) (t : ℕ) :
    normalizedVariance P u v t ≤ limitingVariance P u v :=
  hs.sum_le_tsum (range t) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)

/-- If the series converges, the limiting variance of a pair of distinct
vertices is at least `2`, the squared norm of `q_e`. -/
theorem limitingVariance_ge_two (P : MarkovKernel V) {u v : V} (huv : u ≠ v)
    (hs : Summable (fun j : ℕ => ∑ z, differenceRow P u v j z ^ 2)) :
    2 ≤ limitingVariance P u v := by
  rw [← normalizedVariance_one P huv]
  exact normalizedVariance_le_limitingVariance P u v hs 1

/-- The sum of absolute values of a real row vector. -/
def rowL1 (w : V → ℝ) : ℝ := ∑ x, |w x|

omit [DecidableEq V] in
/-- `rowL1 w` is non-negative. -/
theorem rowL1_nonneg (w : V → ℝ) : 0 ≤ rowL1 w :=
  sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq V] in
/-- Each entry `|w x|` is at most `rowL1 w`. -/
theorem abs_le_rowL1 (w : V → ℝ) (x : V) : |w x| ≤ rowL1 w :=
  single_le_sum (fun y _ => abs_nonneg (w y)) (mem_univ x)

/-- Every entry of `kernelMatrix P ^ j` is non-negative. -/
theorem kernelMatrix_pow_nonneg (P : MarkovKernel V) (j : ℕ) (x y : V) :
    0 ≤ (kernelMatrix P ^ j) x y := by
  induction j generalizing y with
  | zero => rw [pow_zero]; exact zero_le_one_elem x y
  | succ j ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact sum_nonneg fun z _ => mul_nonneg (ih z) (kernelMatrix_nonneg P z y)

omit [DecidableEq V] in
/-- If `A` has non-negative entries and constant row sum `r`, then
`rowL1 (w ᵥ* A) ≤ r * rowL1 w`. -/
theorem rowL1_vecMul_le (A : Matrix V V ℝ) (r : ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (hrow : ∀ x, ∑ y, A x y = r) (w : V → ℝ) :
    rowL1 (w ᵥ* A) ≤ r * rowL1 w := by
  calc
    rowL1 (w ᵥ* A) = ∑ y, |∑ x, w x * A x y| := rfl
    _ ≤ ∑ y, ∑ x, |w x * A x y| := sum_le_sum fun y _ => abs_sum_le_sum_abs _ _
    _ = ∑ y, ∑ x, |w x| * A x y := by
      simp_rw [abs_mul, abs_of_nonneg (hA _ _)]
    _ = ∑ x, ∑ y, |w x| * A x y := sum_comm
    _ = ∑ x, |w x| * r := by simp_rw [← mul_sum, hrow]
    _ = r * rowL1 w := by rw [← sum_mul, mul_comm]; rfl

/-- Multiplication by `kernelMatrix P ^ j` does not increase `rowL1`. -/
theorem rowL1_kernel_pow_le (P : MarkovKernel V) (j : ℕ) (w : V → ℝ) :
    rowL1 (w ᵥ* kernelMatrix P ^ j) ≤ rowL1 w := by
  simpa only [one_mul] using rowL1_vecMul_le (kernelMatrix P ^ j) 1
    (kernelMatrix_pow_nonneg P j) (kernelMatrix_pow_row_sum P j) w

/-- Multiplication by `kernelMatrix P ^ j` preserves the sum of entries of a row. -/
theorem sum_vecMul_kernel_pow (P : MarkovKernel V) (j : ℕ) (w : V → ℝ) :
    ∑ y, (w ᵥ* kernelMatrix P ^ j) y = ∑ x, w x := by
  change (∑ y, ∑ x, w x * (kernelMatrix P ^ j) x y) = _
  rw [sum_comm]
  simp_rw [← mul_sum, kernelMatrix_pow_row_sum, mul_one]

/-- If every entry of `P^ℓ` is at least `ε`, then `rowL1 (w ᵥ* P^ℓ) ≤
(1 - n ε) * rowL1 w` for every row `w` whose entries sum to zero, where `n` is
the number of vertices. -/
theorem rowL1_minorization (P : MarkovKernel V) (ℓ : ℕ) (ε : ℝ)
    (hε : ∀ x y, ε ≤ (kernelMatrix P ^ ℓ) x y)
    (w : V → ℝ) (hw : ∑ x, w x = 0) :
    rowL1 (w ᵥ* kernelMatrix P ^ ℓ) ≤
      (1 - Fintype.card V * ε) * rowL1 w := by
  let A : Matrix V V ℝ := fun x y => (kernelMatrix P ^ ℓ) x y - ε
  have heq : w ᵥ* kernelMatrix P ^ ℓ = w ᵥ* A := by
    ext y
    simp only [vecMul, dotProduct, A, mul_sub, sum_sub_distrib, ← sum_mul, hw,
      zero_mul, sub_zero]
  rw [heq]
  apply rowL1_vecMul_le
  · intro x y; exact sub_nonneg.mpr (hε x y)
  · intro x
    simp only [A, sum_sub_distrib, kernelMatrix_pow_row_sum, sum_const,
      card_univ, nsmul_eq_mul]

/-- On a non-empty vertex set, if every entry of `P^ℓ` is positive, some `ε`
bounds every entry from below and satisfies `0 ≤ 1 - n ε < 1`. -/
theorem exists_minorization [Nonempty V] (P : MarkovKernel V) (ℓ : ℕ)
    (hpos : ∀ x y, 0 < (kernelMatrix P ^ ℓ) x y) :
    ∃ ε : ℝ, 0 ≤ 1 - Fintype.card V * ε ∧
      1 - Fintype.card V * ε < 1 ∧ ∀ x y, ε ≤ (kernelMatrix P ^ ℓ) x y := by
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : V × V => (kernelMatrix P ^ ℓ) p.1 p.2)
  let a := (kernelMatrix P ^ ℓ) p.1 p.2
  have ha : 0 < a := hpos _ _
  have hmin (x y : V) : a ≤ (kernelMatrix P ^ ℓ) x y := hp (x, y)
  have hmass : (Fintype.card V : ℝ) * a ≤ 1 := by
    calc
      (Fintype.card V : ℝ) * a = ∑ y : V, a := by simp
      _ ≤ ∑ y, (kernelMatrix P ^ ℓ) p.1 y := sum_le_sum fun y _ => hmin _ _
      _ = 1 := kernelMatrix_pow_row_sum P ℓ p.1
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  exact ⟨a, sub_nonneg.mpr hmass, sub_lt_self 1 (mul_pos hn ha), hmin⟩

/-- If every entry of `P^ℓ` is at least `ε` and `ρ = 1 - n ε ≥ 0`, then
`rowL1 (w ᵥ* P^(k ℓ + i)) ≤ ρ^k * rowL1 w` for every row `w` whose entries sum
to zero. -/
theorem rowL1_block_decay (P : MarkovKernel V) (ℓ : ℕ) (ε : ℝ)
    (hε : ∀ x y, ε ≤ (kernelMatrix P ^ ℓ) x y)
    (hρ : 0 ≤ 1 - Fintype.card V * ε)
    (w : V → ℝ) (hw : ∑ x, w x = 0) (k i : ℕ) :
    rowL1 (w ᵥ* kernelMatrix P ^ (k * ℓ + i)) ≤
      (1 - Fintype.card V * ε) ^ k * rowL1 w := by
  induction k with
  | zero =>
      simpa only [Nat.zero_mul, Nat.zero_add, pow_zero, one_mul] using rowL1_kernel_pow_le P i w
  | succ k ih =>
      rw [Nat.succ_mul, add_right_comm (k * ℓ) ℓ i, pow_add, ← vecMul_vecMul, pow_succ', mul_assoc]
      exact (rowL1_minorization P ℓ ε hε _ (by rw [sum_vecMul_kernel_pow, hw])).trans
        (mul_le_mul_of_nonneg_left ih hρ)

/-- On a non-empty vertex set, if some positive power of `P` has positive
entries, then `j ↦ rowL1 (w ᵥ* P^j)` is summable for every row `w` whose entries
sum to zero. -/
theorem rowL1_summable_of_positive_power [Nonempty V] (P : MarkovKernel V) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hpos : ∀ x y, 0 < (kernelMatrix P ^ ℓ) x y)
    (w : V → ℝ) (hw : ∑ x, w x = 0) :
    Summable (fun j : ℕ => rowL1 (w ᵥ* kernelMatrix P ^ j)) := by
  obtain ⟨ε, hρ0, hρ1, hε⟩ := exists_minorization P ℓ hpos
  let ρ : ℝ := 1 - Fintype.card V * ε
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  have hg : Summable (fun p : ℕ × Fin ℓ => ρ ^ p.1 * rowL1 w) :=
    Summable.mul_of_nonneg (f := fun k : ℕ => ρ ^ k) (g := fun _ : Fin ℓ => rowL1 w)
      (summable_geometric_of_lt_one hρ0 hρ1) Summable.of_finite
      (fun k => pow_nonneg hρ0 k) (fun _ => rowL1_nonneg w)
  have hs : Summable (fun p : ℕ × Fin ℓ =>
      rowL1 (w ᵥ* kernelMatrix P ^ (p.1 * ℓ + p.2))) :=
    Summable.of_nonneg_of_le (fun p => rowL1_nonneg _)
      (fun p => rowL1_block_decay P ℓ ε hε hρ0 w hw p.1 p.2) hg
  exact (Nat.divModEquiv ℓ).symm.summable_iff.mp hs

/-- If the `rowL1` norms of the rows `w ᵥ* P^j` are summable, so are their dot
products with the rows `v ᵥ* P^j`. -/
theorem row_dotProduct_summable (P : MarkovKernel V) (w v : V → ℝ)
    (hw : Summable (fun j : ℕ => rowL1 (w ᵥ* kernelMatrix P ^ j))) :
    Summable (fun j : ℕ => (w ᵥ* kernelMatrix P ^ j) ⬝ᵥ (v ᵥ* kernelMatrix P ^ j)) := by
  apply Summable.of_norm_bounded (hw.mul_right (rowL1 v))
  intro j
  let A := kernelMatrix P ^ j
  calc
    |∑ z, (w ᵥ* A) z * (v ᵥ* A) z|
        ≤ ∑ z, |(w ᵥ* A) z * (v ᵥ* A) z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |(w ᵥ* A) z| * rowL1 v := by
      refine sum_le_sum fun z _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((abs_le_rowL1 (v ᵥ* A) z).trans (rowL1_kernel_pow_le P j v)) (abs_nonneg _)
    _ = rowL1 (w ᵥ* A) * rowL1 v := (Finset.sum_mul univ (fun z => |(w ᵥ* A) z|) _).symm

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (hd : ∀ x : V, 0 < G.degree x)

/-- Every diagonal entry of the averaging matrix is positive. -/
theorem lazyKernel_matrix_self_pos (x : V) :
    0 < kernelMatrix (lazyKernel G hd) x x := by
  rw [kernelMatrix_apply, lazyKernel_toReal, lazyMass]
  norm_num

/-- Every entry of the averaging matrix corresponding to an edge is positive. -/
theorem lazyKernel_matrix_adj_pos {x y : V} (hxy : G.Adj x y) :
    0 < kernelMatrix (lazyKernel G hd) x y := by
  rw [kernelMatrix_apply, lazyKernel_toReal, lazyMass, if_neg hxy.ne.symm, if_pos hxy]
  have : (0 : ℝ) < G.degree x := Nat.cast_pos.mpr (hd x)
  positivity

/-- If `p` is a walk of length `ℓ` from `x` to `y` and `P` is the averaging
matrix, then `(P^ℓ)_xy > 0`. -/
theorem lazyKernel_walk_pos {x y : V} (p : G.Walk x y) :
    0 < (kernelMatrix (lazyKernel G hd) ^ p.length) x y := by
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
      rw [SimpleGraph.Walk.length_cons, pow_succ', Matrix.mul_apply]
      exact (mul_pos (lazyKernel_matrix_adj_pos G hd hxz) ih).trans_le
        (single_le_sum (fun a _ => mul_nonneg (kernelMatrix_nonneg _ x a)
          (kernelMatrix_pow_nonneg _ p.length a y)) (mem_univ z))

/-- If `(P^j)_xy > 0` and `j ≤ k`, then `(P^k)_xy > 0`, because the walk may
stay at `y`. -/
theorem lazyKernel_power_pos_mono {x y : V} {j k : ℕ} (hjk : j ≤ k)
    (hj : 0 < (kernelMatrix (lazyKernel G hd) ^ j) x y) :
    0 < (kernelMatrix (lazyKernel G hd) ^ k) x y := by
  induction k, hjk using Nat.le_induction with
  | base => exact hj
  | succ k _ ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact (mul_pos ih (lazyKernel_matrix_self_pos G hd y)).trans_le
        (single_le_sum (fun a _ => mul_nonneg (kernelMatrix_pow_nonneg _ k x a)
          (kernelMatrix_nonneg _ a y)) (mem_univ y))

/-- On a finite connected graph, some positive power of the averaging matrix
has all entries strictly positive. -/
theorem lazyKernel_exists_positive_power (hG : G.Connected) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∀ x y, 0 < (kernelMatrix (lazyKernel G hd) ^ ℓ) x y := by
  refine ⟨Fintype.card V, Fintype.card_pos_iff.mpr hG.nonempty, fun x y => ?_⟩
  obtain ⟨p, hp⟩ := (hG x y).exists_isPath
  exact lazyKernel_power_pos_mono G hd hp.length_lt.le (lazyKernel_walk_pos G hd p)

/-- The row `q_eᵀ P^j` is the row `q_eᵀ` multiplied by `P^j`. -/
theorem differenceRow_eq_vecMul (P : MarkovKernel V) (u v : V) (j : ℕ) :
    differenceRow P u v j = differenceRow P u v 0 ᵥ* kernelMatrix P ^ j := by
  ext z
  simp only [differenceRow, pow_zero, Matrix.one_apply, vecMul, dotProduct, sub_mul,
    sum_sub_distrib, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]

/-- Lemma T2.3 (summability): for the averaging rule of a finite connected
graph, the series defining `V_∞(u, v)` converges for all vertices `u` and `v`. -/
theorem lazyKernel_variance_summable (hG : G.Connected) (u v : V) :
    Summable (fun j : ℕ => ∑ z, differenceRow (lazyKernel G hd) u v j z ^ 2) := by
  haveI : Nonempty V := hG.nonempty
  obtain ⟨ℓ, hℓ, hpos⟩ := lazyKernel_exists_positive_power G hd hG
  let w := differenceRow (lazyKernel G hd) u v 0
  have hw := rowL1_summable_of_positive_power (lazyKernel G hd) ℓ hℓ hpos w
    (differenceRow_row_sum (lazyKernel G hd) u v 0)
  simpa only [w, dotProduct, ← differenceRow_eq_vecMul, pow_two] using
    row_dotProduct_summable (lazyKernel G hd) w w hw

end GraphStability
