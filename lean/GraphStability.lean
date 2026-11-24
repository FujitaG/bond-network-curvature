import GraphStability.Amplification
import GraphStability.BlockDecomposition
import GraphStability.Covariance
import GraphStability.CurvatureComparison
import GraphStability.EffectiveCurvature
import GraphStability.EffectiveLifetime
import GraphStability.Extrema
import GraphStability.FiniteTransport.CostTransform
import GraphStability.FiniteTransport.LinearDuality
import GraphStability.FiniteTransport.ProbabilityMatrices
import GraphStability.GaussianAsymptotics
import GraphStability.GaussianLaw
import GraphStability.GaussianNoise
import GraphStability.GaussianTail
import GraphStability.LazyWalk
import GraphStability.Lifetime
import GraphStability.LifetimeLower
import GraphStability.LifetimeRate
import GraphStability.LifetimeUpper
import GraphStability.MinimumPerturbation
import GraphStability.Process
import GraphStability.SpectralVariance
import GraphStability.Transport
import GraphStability.TransportDuality
import GraphStability.Variance
import GraphStability.VarianceLimit

/-!
# Curvature, noise, and lifetime on a finite graph (Supplementary Theory)

* Transport and discrete Ricci curvature (Section T1): `Transport`, `LazyWalk`,
  duality for transport distance in `FiniteTransport` and `TransportDuality`,
  and Theorem 1 in `Amplification`.
* The process and the lifetime (Section T2.1): `Process`, `GaussianNoise`, and
  `Lifetime`.
* Variance of an edge difference and effective curvature (Sections T2.2 to
  T2.4): `GaussianLaw`, `Variance`, `MinimumPerturbation`, `VarianceLimit`, and
  `EffectiveCurvature`.
* Bounds on the mean lifetime (Sections T2.5 and T2.6): `Extrema`,
  `GaussianTail`, `LifetimeLower`, and `EffectiveLifetime` for Theorem 2;
  `BlockDecomposition` and `LifetimeUpper` for Lemma T2.5; `GaussianAsymptotics`
  and `LifetimeRate` for Theorem 3.
* Covariance equation and comparisons (Sections T2.7 and T2.8): `Covariance`,
  `CurvatureComparison`, and `SpectralVariance`.
-/
