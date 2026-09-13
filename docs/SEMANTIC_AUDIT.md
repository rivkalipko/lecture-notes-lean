# Semantic audit of the formal statements

Audit date: 2026-09-13. Starting revision: `2c5ec26724c924547fd45b501c889f04a09b8576`.

The review covered definitions, theorem statements, and proof arguments in
all 31 modules present at that revision. It compared the mathematical objects,
quantifiers, hypotheses, and conclusions with the corresponding passages in
the six source PDFs. `BernoulliModel` was added as a concrete check of the
density and score definitions. The project now has 32 modules.

This review concerns the included formalization. It does not establish that
every item in the notes has been transcribed. The [coverage ledger](COVERAGE.md)
continues to identify missing and restricted results. A successful Lean build
checks a proposition once formulated; it cannot establish that the proposition
is the intended one.

## Corrections made

1. **CDF definition and measurability (L1 Definition 8).** Previously `cdfOf`
   directly used Mathlib's `cdf (P.map X)`, and the exported CDF properties
   did not require measurability of `X`. Mathlib gives its CDF object the usual
   shape even for nonprobability inputs, where it need not describe the input
   measure. `cdfOf P X x` now directly means `P.real {w | X w <= x}`.
   `cdfOf_eq_cdf` proves agreement with the library under `AEMeasurable X P`,
   and the CDF properties carry that hypothesis.
2. **Exponential families (L5 Definition 2).** The old predicate only asserted
   an algebraic exponential representation; it also accepted negative or
   unnormalized functions. That predicate is now named `HasExponentialForm`.
   `ExponentialFamily` additionally requires nonnegative, integrable,
   normalized densities with respect to a common reference measure and
   measurable data factors with a nonnegative base factor and positive
   normalizing factor. `ExponentialFamily.isProbabilityMeasure` proves that
   these densities define probability measures. The purely algebraic
   factorization results remain available with their explicit interpretation.
3. **Likelihood, score, and MLE argument order (L6 pp3–4).** All three now
   consistently take data before parameters. Thus `Score (LogLikelihood f) x
   theta` differentiates in the parameter. The old first-order lemma concerned
   a generic function's derivative; it is retained under that descriptive
   name. `score_zero_at_interior_mle` now concludes that the actual
   log-likelihood score is zero from a positive differentiable likelihood at
   an interior local maximum. Log-likelihood maximization is stated using
   `IsMLE` on both sides.
4. **Asymptotic normality (L5 pp6–7).** The definition uses the canonical
   normal probability space on the real line, removing the requirement to
   supply a Gaussian random variable on the original sample space. It allows
   zero asymptotic variance, requires measurable estimators, and requires an
   eventually nonzero scaling sequence. The last condition excludes zero
   rates and keeps the reciprocal scale defined eventually.
5. **Unbiased Cramér–Rao (L6 Theorem 2).** The algebraic helper is now named
   `cramer_rao_unbiased_from_score_identity`. The new
   `RegularDensity.cramer_rao_unbiased` assumes actual unbiasedness for every
   parameter in the open domain and proves the derivative of the mean is one.
   Unbiasedness at a single parameter would not justify that step.
6. **Sampling probabilities and finite moments.** Horvitz–Thompson theorem
   statements now explicitly require a nonempty population and nonzero
   dividing inclusion moments. `horvitzThompson_design_unbiased` and
   `horvitzThompson_design_variance` specialize to an actual probability
   measure on subsets, with positive marginal inclusion probabilities; their
   formulas use actual marginal and joint event probabilities. The elementary
   variance scaling/translation wrappers now require square integrability.
   Independence of the normal sample mean and sample variance now explicitly
   requires at least two observations, avoiding the one-observation default
   value of the sample-variance formula.
7. **Additional statement alignment.** `slutsky_mul_zero` explicitly records
   the convergence-in-probability conclusion following L3 Theorem 8.
   Comments clarify the finite-risk interpretation of real integrals, null
   conditional-probability conventions, positive t/F degrees of freedom, and
   the shift from the notes' one-based sequences to Lean's zero-based indices.

These changes address formulation or interpretation gaps. They do not replace
failed proofs by assumptions or count algebraic identities as general
statistical theorems.

## Review by topic

| Modules reviewed | Mathematical checks and limits |
| --- | --- |
| `Foundations`, `ProbabilityLaws`, `ConditionalExpectation` | Event products, intersections and complements; conditional-probability direction and denominators; CDF endpoints and right continuity; L1/L2 hypotheses; almost-everywhere equalities; conditional squared-loss orthogonality. Best prediction remains restricted to square-integrable competitors because the risk is real-valued. |
| `Sampling`, `SamplingMoments`, `FinitePopulation` | Mean denominator `n`, sample-variance denominator `(n : Real) - 1`; positivity of sample/population sizes; off-diagonal and diagonal covariance terms; HT population-mean normalization `1/N`; actual uniform-subset design and inclusion probabilities; finite-population correction, including one draw and the census case. |
| `NormalSampling`, `NormalSamplingDistribution`, `GaussianQuadraticForms`, `GaussianMahalanobis`, `NormalFStatistic`, `ChiSquaredMoments`, `NormalVarianceRisk` | Independence is joint where needed; mean variance is `v/n`; residual rank and t degrees of freedom are `n-1`; nonzero random denominators follow almost surely; F statistic includes the population-variance ratio; matrix projections require symmetry and idempotence; Mahalanobis covariance is positive definite; fourth normal moment is proved, not assumed; `v^2` denotes the notes' fourth power of the standard deviation. |
| `Inequalities`, `Concentration` | Hölder absolute values and conjugate exponents; Markov/Chebyshev thresholds; Hoeffding exponent and interval width; independent bounded observations. The subgaussian auxiliary bound at zero variance proxy is only its totalized, possibly uninformative extension; the statistical Hoeffding formulas require positive interval width and sample size. |
| `LargeSample`, `Convergence`, `WeakLaw`, `CramerWold`, `MultivariateCLT`, `DeltaMethod`, `StochasticOrder` | Centering, square-root scaling, finite moments, common versus separate probability spaces, all five convergence implications, Slutsky division limit, every linear projection in Cramér–Wold, transformed delta-method variance, measurability of the divided difference, and uniform-in-n stochastic-order quantifiers. The multivariate CLT specifies the target through Gaussian projection laws; it does not construct a target from a covariance matrix. The source CDF characterization of weak convergence still lacks a formal equivalence bridge. |
| `EmpiricalDistribution`, `Bootstrap` | The CDF uses `<=`; indicator expectation and variance are actual probabilities; consistency and concentration quantify over a fixed threshold. They do not imply the still-missing uniform DKW result. Bootstrap samples use independent indices drawn with replacement from the uniform index law. |
| `Estimation`, `EstimationTheory`, `Sufficiency`, `RaoBlackwell` | Measurable statistics, integrable unbiasedness, parameter independence of factors and estimators, correct shrinkage bias and variance coefficients, and nonzero likelihood ratios. Finite sufficiency concerns conditional masses on positive common support; minimality is the fiber reduction criterion. General sufficiency uses one conditional kernel for the model, with parameter-specific exceptional null sets. The Rao–Blackwell conclusion is `exists g, for all theta`, so it gives one estimator for the entire model. |
| `Information`, `RegularDensity`, `RegularCramerRao` | The covariance bound includes zero variance. Positive finite information and score second moments are explicit. Density normalization is differentiated under integrable bounds twice. The estimator's mean derivative is derived using an integrable bound on the estimator times the density derivative. An open domain and a parameter in that domain appear in the results. These assumptions are stronger and more explicit than the insufficient log-Hessian domination condition printed in the notes. |

## Concrete check against the notes

`BernoulliModel` constructs a regular Bernoulli density on `{0,1}` for
`0 < p < 1`, with counting measure, first derivative `-1` or `1`, and second
derivative zero. Thus the density assumptions have a concrete inhabitant on a
nonempty domain. It also proves the normalized exponential representation
from L5 p10 and checks that the common likelihood API gives the scores
`-1/(1-p)` and `1/p` while holding the observation fixed.

The information calculation yields `1/(p*(1-p))` both as a weighted density
integral and as Fisher information under the induced probability measure,
matching L6 Example 7. The observation is proved unbiased, and the general
unbiased Cramér–Rao theorem is applied to this actual estimator. These checks
exercise the definitions together, including their parameter domains.

L5 p10 and L6 pp4 and 6 were checked against rendered pages. The source's
uniform MLE example contains inconsistent strict/closed endpoint indicators;
this is recorded in [SOURCE_AUDIT.md](SOURCE_AUDIT.md). The formalization does
not claim to prove that uncorrected example.

## Verification and remaining scope

The release check is `bash scripts/check.sh`: every module is imported and
built, the source scan rejects proof placeholders and forbidden shortcuts,
and the transitive dependency audit rejects all axioms except Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

Full lecture coverage remains incomplete, particularly Lindeberg–Feller,
Glivenko–Cantelli/DKW, general density factorization and minimal sufficiency,
distribution transformations, and several examples and algorithms. Some
included proofs apply Mathlib results instead of reproducing the lecture proof
line by line. No claim of complete transcription follows from this audit.
