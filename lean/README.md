# Network curvature: Lean proofs

The package proves every lemma, proposition, and theorem of the Supplementary
Theory (Sections T1 and T2) and of Supplementary Methods M1. It is written in
[Lean 4](https://lean-lang.org) on top of
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Where to start

Read [`Paper.lean`](Paper.lean), which restates the results under their
numbers in the paper. The proofs rest on two libraries; the docstrings of
[`GraphStability.lean`](GraphStability.lean) and
[`RhombicFamily.lean`](RhombicFamily.lean) describe their modules.

| Library | Content |
| --- | --- |
| `GraphStability` | Transport distance and discrete Ricci curvature on a finite graph, averaging with Gaussian noise, the variance of an edge difference, effective curvature, and the mean lifetime (Supplementary Theory). |
| `RhombicFamily` | The designs derived from the rhombic-dodecahedral parent cell, the two admissibility conditions, and the classification of admissible designs into seven symmetry classes (Supplementary Methods M1). |

[`Audit.lean`](Audit.lean) checks that no declaration of `GraphStability`,
`RhombicFamily`, or `Paper` uses `sorry` or any axiom beyond `propext`,
`Classical.choice`, and `Quot.sound`.

## Results

`G` is a finite connected simple graph with at least two vertices, and `P` is
its averaging rule (the 1/2-lazy random walk). Names in the second column are
in the namespace `Paper`; the third column lists the main supporting
declarations of `GraphStability` or `RhombicFamily`.

### Supplementary Theory

| Paper | `Paper.lean` | Main library declarations |
| --- | --- | --- |
| Section T1.1, every vertex has a neighbour and there is an edge | `degree_pos`, `edge_exists` | |
| Eq. (S1), one averaging step | `equation_S1` | `markovOperator` |
| Eq. (S2), averaging rule | `equation_S2` | `lazyKernel`, `lazyKernel_toReal` |
| Eq. (S4), 1-Wasserstein distance attained | `equation_S4` | `exists_optimal_transportPlan` |
| Eq. (S5), discrete Ricci curvature | `equation_S5` | `ricciCurvature` |
| Eq. (S7), 1-Lipschitz functions | `equation_S7` | `IsOneLipschitz` |
| Lemma T1.1, duality for transport distance | `lemma_T1_1` | `exists_optimal_lipschitz_function`, `isGreatest_abs_pairing` |
| Theorem 1, negative curvature and amplification modes | `theorem_1` | `isGreatest_edge_amplification`, `negative_curvature_iff_edge_amplification` |
| Eq. (S14), the process and its fresh noise | `equation_S14`, `equation_S14_noise`, `process_exists` | `GaussianAveragingProcess`, `exists_gaussianAveragingProcess` |
| Eqs (S15), (S51), lifetime and mean lifetime | `equation_S15`, `equation_S51` | `lifetime`, `meanLifetime`, `meanLifetime_eq_lintegral` |
| Eq. (S19) and Lemma T2.1, distribution of an edge difference | `equation_S19`, `lemma_T2_1` | `differenceRow`, `normalizedVariance`, `edgeDiff_gaussian` |
| Lemma T2.2, sum of squared perturbations needed to reach the threshold | `lemma_T2_2` | `isLeast_perturbation_sum_sq` |
| Lemma T2.3, `2 ≤ V_∞(e) < ∞` | `lemma_T2_3` | `lazyKernel_variance_summable`, `limitingVariance_ge_two` |
| Eqs (S34)–(S36), equivalent bond and effective curvature | `equation_S34`, `equation_S35`, `equation_S36` | `effectiveCurvature`, `effectiveCurvature_equivalentBond`, `eq_two_div_effectiveCurvature` |
| Eqs (S38), (S39), extrema over edges | `equation_S38`, `equation_S39` | `maxLimitingVariance`, `edge_extrema` |
| Lemma T2.4, two-sided Gaussian tail | `lemma_T2_4` | `gaussian_tail_bound` |
| Theorem 2, lower bound on the mean lifetime | `theorem_2` | `meanLifetime_lower_of_maxLimitingVariance`, `lifetime_probability_le_of_maxLimitingVariance` |
| Eq. (S53) and the bound following it, from a lower bound on the effective curvature of every edge | `equation_S53` | `meanLifetime_lower_of_effectiveCurvature`, `lifetime_probability_le_of_effectiveCurvature` |
| Lemma T2.5, survival probabilities at fixed time intervals | `lemma_T2_5`, `mean_lifetime_finite` | `blockProbability`, `abs_add_freshPart_probability`, `break_probability_of_past_event`, `lifetime_gt_mul_le_pow`, `meanLifetime_upper_bound` |
| Theorem 3, exponential growth rate of the mean lifetime | `theorem_3`, `theorem_3_limit` | `meanLifetime_rate_uniform` |
| Eqs (S68)–(S70), centring and covariance recursion | `equation_S68`, `equation_S69`, `equation_S70` | `centeredValues_update`, `centeredValues_normalized_second_moment`, `normalizedCovariance_succ` |
| Proposition T2.6, covariance equation | `proposition_T2_6` | `covarianceEquation_limitingCovariance`, `covarianceEquation_unique`, `limitingVariance_eq_covariance` |
| Proposition T2.7, a uniform lower bound on discrete Ricci curvature | `proposition_T2_7` | `le_effectiveCurvature_of_le_ricciCurvature` |
| Eq. (S76), regular graphs and the spectral gap | `equation_S76` | `regular_spectral_variance`, `regular_effectiveCurvature_ge_spectralGap` |

### Supplementary Methods M1

| Paper | `Paper.lean` | Main library declarations |
| --- | --- | --- |
| Section M1.1, parent cell | `parent_cell` | `coordinate`, `incident`, `endpoints`, `shortDiagonals_iff_common_nodes` |
| Definition 1, designs and their skeletons | `definition_1` | `IsPattern`, `Design`, `skeletonGraph` |
| Section M1.1, 108 cross-linking patterns and 6,912 designs | `design_counts` | `card_patterns`, `card_patterns_of_size`, `card_design` |
| Definition 2, ligand molecules and local environments | `definition_2` | `ligands`, `localEnvironment` |
| Definition 3, conditions (E) and (D) | `definition_3` | `UniformLocalEnvironment`, `HasMinimumDegreeThree`, `Admissible` |
| Section M1.3, 80 designs satisfying (E) and 31 admissible designs | `admissible_counts` | `card_uniform`, `card_admissible` |
| Section M1.4, the 48 symmetries and equivalence | `symmetries`, `equivalence` | `Symmetry`, `siteAction`, `nodeAction`, `diagonalAction`, `transform`, `Equivalent` |
| Proposition M1.1, classification | `proposition_M1_1` | `representative_admissible`, `representatives_inequivalent`, `unique_representative` |
| Table S3 | `table_S3_patterns`, `table_S3_designs`, `table_S3` | `representative`, `representative_environments`, `representative_stabilizer_orders`, `representative_class_sizes`, `representative_skeleton_counts` |
| Lemma M1.2, consequences | `lemma_M1_2` | `admissible_consequences` |

## Scope

Table S3 is formalized apart from the point-group symbols. The counts 273 and
266 and the remark that both conditions are needed are checked by the
enumeration script in [`../enumeration`](../enumeration).

Proofs that take a different route from the paper:

- **Lemma T1.1.** Section T3 constructs an optimal 1-Lipschitz function from
  an optimal transport plan. Here duality follows from separating convex sets;
  the cost transform (S79) produces a 1-Lipschitz function, and compactness
  gives the maximizer.
- **Proposition T2.7 and equation (S76).** Proposition T2.7 uses an optimal
  transport plan in place of Theorem 1. For (S76), each Gershgorin disc of the
  averaging matrix has centre and radius `1/2`, so its real eigenvalues lie in
  `[0, 1]`. Constancy of the eigenvectors with eigenvalue `1` follows from
  Lemma T2.3.
- **Proposition M1.1 and Lemma M1.2.** After reduction to the empty pattern and
  the nine complete patterns, every complete pattern is checked with every
  deletion set in the Lean kernel.

## Conventions

The section "Standing assumptions and notation" of `Paper.lean` explains the
notation of the statements.

- `ricciCurvature G P x y` is `1 - W₁(P x, P y) / d(x, y)`; on an edge
  `d(x, y) = 1`, which gives (S5).
- `limitingVariance` is defined as an infinite sum. `lemma_T2_3` proves that it
  converges, so its value is the limit `V_∞(e)` of `V_t(e)`.
- `effectiveCurvature V = 1 - √(1 - 2/V)` applies for `V ≥ 2`, which holds for
  every edge by `lemma_T2_3`.
- `lifetime` is the infimum in `ℕ∞` of the rounds in which an edge difference
  reaches the threshold. Since `f₀ = 0`, a positive threshold can first be
  reached only at `t ≥ 1`, as in `equation_S15`.
- `meanLifetime` is defined as `∑_t ℙ(τ_θ > t)`, taking values in `[0, ∞]`.
  `equation_S51` identifies it with `𝔼[τ_θ]`, and `mean_lifetime_finite`
  shows that it is finite and at least `1` for `θ > 0` and `σ > 0`.

## Build

Install [elan](https://github.com/leanprover/elan). Then, in this directory:

```sh
lake exe cache get   # download the compiled Mathlib
lake build
```

`lake build` compiles both libraries, `Paper.lean`, and the axiom audit. The
audit reports the number of declarations checked and the axioms used.

The finite checks of `RhombicFamily` run in the Lean kernel and dominate the
build. `RhombicFamily.Symmetry` needs about 13 GB of memory, and `Cell`,
`Classification`, `Consequences`, and `Counts` between 7 and 9 GB each.
`lake build` checks the last three in parallel, which needs about 21 GB. If
the symmetry check fits in memory but the parallel build does not, build them
one at a time first:

```sh
lake build RhombicFamily.Symmetry
lake build RhombicFamily.Classification
lake build RhombicFamily.Consequences
lake build RhombicFamily.Counts
lake build
```

In this order, and with the compiled Mathlib in place, the build takes about
ten minutes.

Lean `4.24.0` and Mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Licence

Copyright 2026 Daishi Fujita. Released under the Apache License 2.0; see
[LICENSE](../LICENSE).
