# MIT 14.380 lecture notes in Lean

This is an **incomplete formalization** of thirteen supplied lecture notes.
The included results have Lean proofs, using Mathlib's measures, integrals,
conditional expectations, independence, and convergence of probability laws.
The project does not yet formalize every definition, theorem, example, or proof
in the PDFs.

The [coverage ledger](docs/COVERAGE.md) lists every numbered theorem and
distinguishes proved, restricted, and missing results. Major remaining work
includes Lindeberg–Feller, Glivenko–Cantelli and DKW, and sufficiency for general
dominated continuous models, constrained vector MLE/Wilks asymptotics,
general/vector Bernstein–von Mises, model-specific bootstrap validity, and several examples. A scalar IID MLE normality theorem and scalar Wilks theorem are proved under explicit
derivative, moment, consistency, and interior-maximization conditions. A scalar
posterior approximation theorem is proved under explicit local quadraticity
and domination conditions, verified for normal-mean kernels and bounded
continuous priors. The James–Stein exact risk and strict dominance theorem is
proved, including inverse-square integrability and the singular limit. The normal
minimax lower bound, minimaxity of the identity and James–Stein rules, and
positive-part dominance and minimaxity are also proved among measurable rules. A finite
positive-support sufficiency theorem is proved and labeled with that restriction.

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
  `StochasticOrder`.
* Empirical distributions: `EmpiricalDistribution`, `Bootstrap`,
  `QuantileConvergence`, `BootstrapIntervals`.
* Estimation: `Estimation`, `Sufficiency`, `EstimationTheory`, `Information`,
  `RegularDensity`, `RegularCramerRao`, `RaoBlackwell`, `BernoulliModel`.
* MLE and testing: `MLEConsistency`, `Testing`, `NeymanPearson`,
  `MonotoneLikelihoodRatio`, `LikelihoodRatio`, `AsymptoticTests`,
  `LogisticRegression`, `MLEAsymptotics`, `IIDScoreAsymptotics`, `WilksAnalytic`,
  `ExponentialMLE`, `LogisticMultivariate`, `BoundaryNormalMLE`, `VectorWald`.
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
