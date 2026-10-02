# MIT 14.380 lecture notes in Lean

This is an **incomplete formalization** of thirteen supplied lecture notes.
The included results have Lean proofs, using Mathlib's measures, integrals,
conditional expectations, independence, and convergence of probability laws.
The project does not yet formalize every definition, theorem, example, or proof
in the PDFs.

The [coverage ledger](docs/COVERAGE.md) lists every numbered theorem and
distinguishes proved, restricted, and missing results. Major remaining work
includes the sharp DKW inequality, the unrestricted minimal-sufficiency
criterion, curved-restriction Wilks asymptotics, general/vector
Bernstein–von Mises, model-specific bootstrap distributional validity, and
several examples. Lindeberg–Feller, Lyapunov, and Glivenko–Cantelli are now
proved, including non-identically distributed observations for the CLT and
distributions with atoms for uniform CDF convergence. The CDF characterization
of weak convergence and measurability of the empirical supremum error are proved.

General Fisher–Neyman factorization is proved for sigma-finitely dominated
standard Borel experiments, with parameter-dependent supports and arbitrary
measurable carriers. Exponential-family canonical sums are sufficient in the
actual IID product experiment, and the normal sample mean is minimal sufficient
with known positive variance. Likelihood-ratio recovery also gives a general
minimality criterion relative to a countable dominating mixture.

Scalar and vector IID MLE normality are proved under explicit derivative,
moment, consistency, and interior-maximization conditions. The vector theorem
keeps score covariance separate from mean curvature, gives the sandwich limit,
and specializes to inverse information under the information identity. A scalar
posterior approximation theorem is proved under explicit local quadraticity
and domination conditions, verified for normal-mean kernels and bounded
continuous priors. The James–Stein exact risk and strict dominance theorem is
proved, including inverse-square integrability and the singular limit. The normal
minimax lower bound, minimaxity of the identity and James–Stein rules, and
positive-part dominance and minimaxity are also proved among measurable rules.

Randomized Neyman–Pearson threshold existence and calibration are proved,
including alternatives with mass where the null density is zero. The MLR
existence theorem permits discrete statistics and cutoffs outside their range,
under a common strictly positive density assumption. Exact normal, Student,
and chi-square confidence intervals, normal test power, and Gaussian credible
intervals are proved using a generalized-inverse quantile. Bootstrap critical
values and interval coverage are proved conditional on convergence of the
conditional CDFs to an atomless strictly increasing limiting CDF. The
model-specific conditional limit is still required.

The exponential-rate example includes the global likelihood maximum, the
information identities, consistency from the IID law, asymptotic normality
with variance equal to the squared rate, and plug-in variance consistency.
The fixed-design logistic example now identifies the full likelihood derivatives,
proves global optimality of score roots and uniqueness under full column rank,
and proves nonexistence of a finite maximum under complete separation. Vector
Wald limits and coverage follow from a supplied Gaussian estimator limit and
consistent covariance estimates; covariance inversion, plug-in information,
sandwich consistency, and both bivariate ellipse projections are proved. The
constrained normal-mean example includes its actual likelihood maximum and
the nonnormal boundary limit derived from IID normal observations.

The scalar pseudo-MLE theorem permits distinct score variance and mean curvature,
yielding the sandwich variance under explicit regularity and consistency assumptions.
Observed-curvature consistency is proved with an integrable derivative envelope.
The Neyman–Scott example includes actual likelihood maximization and the inconsistent
variance limit, along with a consistent correction. Exact normal likelihood-ratio
calibration and two-sided UMP nonexistence in the normal-observation experiment are
proved. HPD existence now handles density plateaus on the real line, and quantile
reparameterization covers continuous non-surjective increasing maps and decreasing
maps under explicit distributional conditions.
The uniform-endpoint example includes the exact maximum law and moments,
consistency, and a zero square-root-scale limit. Estimated-information intervals
have separate proved frequentist-coverage and posterior-content results under
their stated sampling, approximation, and positivity conditions.

The [source audit](docs/SOURCE_AUDIT.md) records mathematical corrections and
extra hypotheses. The thirteen source PDFs are preserved unchanged. Compilation
certifies the formal statements; it does not establish complete coverage or
literal agreement with an incorrect statement in the notes.

The [semantic audit](docs/SEMANTIC_AUDIT.md) reviews the included statements,
documents corrected definitions and domain conditions, and checks the density
frameworks against a concrete Bernoulli model from the notes.

The September 29 export adds Lectures 7–13; Lectures 1–6 are unchanged.
[NEW_NOTES_AUDIT.md](docs/NEW_NOTES_AUDIT.md) records source corrections,
including insufficient MLE assumptions, non-strict MLR power monotonicity,
and the invalid use of a two-sided UMP test in a confidence-interval example.
[NEW_NOTES_COVERAGE.md](docs/NEW_NOTES_COVERAGE.md) distinguishes full results,
restricted results, intermediate arguments, and unproved claims in these notes.

## Check the proofs

Install Lean using Elan, then run:

```sh
lake exe cache get
bash scripts/check.sh
```

Lean and Mathlib are pinned in `lean-toolchain` and `lake-manifest.json`.
The check script builds every source module and runs two audits:

* `scripts/check_sources.py` rejects placeholder tokens, unsafe proof shortcuts,
  and modules omitted from the root import file.
* `Audit.lean` follows the axiom dependencies of every project declaration,
  including private and compiler-generated declarations. It permits only
  `propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx`, project
  axioms, and any other axiom dependency.

GitHub Actions runs the same checks. A successful check means the **included
proofs** passed; it does not turn a missing coverage entry into a proved result.

## Organization

* Probability and moments: `Foundations`, `ProbabilityLaws`,
  `ConditionalExpectation`.
* Gaussian distributions: `GaussianQuadraticForms`, `GaussianMahalanobis`,
  `ChiSquaredMoments`.
* Sampling: `Sampling`, `SamplingMoments`, `NormalSampling`,
  `NormalSamplingDistribution`, `NormalFStatistic`, `NormalVarianceRisk`,
  `FinitePopulation`.
* Inequalities and limits: `Inequalities`, `Concentration`, `LargeSample`,
  `Convergence`, `WeakLaw`, `CramerWold`, `MultivariateCLT`, `DeltaMethod`,
  `StochasticOrder`, `CDFConvergence`, `VectorScoreCLT`,
  `LindebergAnalytic`, `LindebergBounds`, `LindebergFeller`, `Lyapunov`.
* Empirical distributions: `EmpiricalDistribution`, `Bootstrap`,
  `EmpiricalUniform`, `EmpiricalSupMeasurable`, `BootstrapMoments`,
  `QuantileConvergence`, `BootstrapIntervals`.
* Estimation: `Estimation`, `Sufficiency`, `EstimationTheory`, `Information`,
  `RegularDensity`, `RegularCramerRao`, `RaoBlackwell`, `BernoulliModel`;
  dominated sufficiency: `DominatedSufficiency`, `DominatingMixture`,
  `MixtureSufficiency`, `FisherNeyman`, `SigmaFiniteFactorization`,
  `FisherNeymanGeneral`, `ExponentialFamilySufficiency`, `MinimalSufficiency`,
  `MixtureMinimalSufficiency`, `NormalSufficiency`, `UniformSufficiency`.
* MLE and testing: `MLEConsistency`, `Testing`, `NeymanPearson`,
  `MonotoneLikelihoodRatio`, `LikelihoodRatio`, `AsymptoticTests`,
  `LogisticRegression`, `MLEAsymptotics`, `IIDScoreAsymptotics`, `WilksAnalytic`,
  `ExponentialMLE`, `LogisticMultivariate`, `BoundaryNormalMLE`, `VectorWald`,
  `VectorScoreAsymptotics`, `VectorMLE`, `VectorWilks`, `ConstrainedVectorMLE`,
  `NormalUnknownVarianceMLE`.
  Threshold existence and exact power: `Quantiles`, `NeymanPearsonExistence`,
  `MLRExistence`, `NormalTestPower`.
* Confidence and Bayesian inference: `ConfidenceSets`, `WilsonInterval`, `EllipseProjection`,
  `QuantileIntervals`, `SamplingAtomlessness`, `NormalConfidenceIntervals`, `BayesianUpdating`,
  `NormalConjugacy`, `BetaConjugacy`, `GammaConjugacy`, `ExponentialConjugacy`,
  `PosteriorAsymptotics`, `NormalPosteriorLimit`, `HighestDensity`, `HighestDensityExistence`,
  `BayesianDecision`, `BayesianTesting`.
* Decision theory: `DecisionTheory`, `NormalMeansDecision`, `GaussianStein`,
  `NormalSteinRisk`, `RegularizedStein`, `JamesSteinRisk`, `JamesStein`,
  `SteinDecision`, `EmpiricalBayesStein`, `NormalDecisionExamples`,
  `GaussianBayesRisk`, `NormalMinimax`, `GaussianReflection`, `PositivePartStein`.

Some proofs follow the notes' algebra or conditional-expectation argument;
others apply established Mathlib theorems, notably SLLN, scalar CLT, Jensen,
Hölder, Gaussian independence, and the subgaussian bound used for Hoeffding.
These are checked formal proofs, not line-by-line transcriptions of every
source proof.
