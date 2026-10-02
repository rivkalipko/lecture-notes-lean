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
# September 29 additions

The new Lectures 7–13 were compared against the supplied PDFs, using both
layout-preserving extraction and rendered checks of the key theorem pages.
The original Lectures 1–6 are unchanged. See
[NEW_NOTES_AUDIT.md](NEW_NOTES_AUDIT.md) for the new mathematical corrections and
[NEW_NOTES_COVERAGE.md](NEW_NOTES_COVERAGE.md) for every new numbered theorem's
status. The new modules use `autoImplicit false` so a misspelled identifier
cannot silently become an extra theorem parameter.

The audit checks that tests are measurable `[0,1]`-valued rejection probabilities;
density power is linked to actual model measures; MLR power is nonincreasing;
test inversion proves coverage inequalities in the correct direction; Pratt
uses a jointly measurable confidence graph; Bayesian risk uses the actual
posterior kernel; extended nonnegative risks handle infinity; and normal
shrinkage risk is derived from Gaussian laws and moment conditions. Generic
argmax consistency requires uniform criterion control and separation. The
scalar IID score-root and Wilks results now derive the CLT, LLNs, and likelihood
expansion from explicit derivative and moment hypotheses. They retain
consistency and measurable interior maximization as assumptions. Normal conjugacy identifies an
actual Gaussian law of the normalized product of kernels.

The scalar posterior theorem derives normalized L1 convergence from domination
and convergence of the unnormalized local kernels. An exact affine change of
variables links these kernels to the posterior distribution of the centered,
scaled parameter. Its event bound is uniform over all measurable sets. A
separate theorem records almost-sure convergence under almost-sure pathwise
conditions. A normal-mean example verifies the quadratic expansion and envelope
for bounded continuous integrable priors positive at the true parameter. The
hypotheses are deliberately stronger than an unspecified general regularity
claim; general/vector Bernstein–von Mises is not claimed as proved.

Beta and Gamma conjugacy identify actual probability measures and calculate
moments from normalized densities. Beta(1,1) is proved equal to Lebesgue measure
restricted to [0,1]. The Gamma proofs distinguish rate from scale and ignore only
the null singleton at zero. Integer moments have integrability proofs before
they are used to calculate variances. Exponential-family conjugacy checks prior
and posterior normalizers; the finite-sample kernel product verifies the sample
size and sufficient-statistic updates. HPD optimality compares sets with at
least the threshold region’s posterior content, so calibration is necessary
before claiming optimality at a prescribed credible level. Posterior-odds testing
minimizes actual integral loss and distinguishes unequal error costs.

The James–Stein proof now starts with integration by parts against the actual
Gaussian density. It proves coordinate Stein identities under the product
normal law and the unbiased risk formula for bounded smooth corrections.
For gε(y) = −a y/(S+ε), where S is the sum of coordinate squares and
a = (p−2)v, the regularized risk is

    p v − a² E[S/(S+ε)²] − 2 a p v ε E[1/(S+ε)²].

Nonnegativity of risk bounds the first expectation uniformly; Fatou proves
integrability of 1/S. The origin is null under the nondegenerate normal law.
Dominated convergence proves the exact singular risk formula, with the loss
bounded by twice the unshrunk squared loss plus 2a²/S. Positivity of E[1/S]
then gives strict improvement for p ≥ 3 and v > 0. All squared losses used
with real integrals are proved integrable. The extended-real risk bridge
establishes dominance and inadmissibility using the repository's definitions.
The centered calculation gives E[1/S] = 1/((p−2)v) and verifies the empirical
Bayes noise-fraction formula. The separate minimax and positive-part proofs
are described below.

The scalar MLE/Wilks extension uses a measurable divided difference, avoiding
an unjustified measurable choice of a mean-value point. Its value at a
coincident endpoint preserves the exact score identity. Finite-sample curvature
may vanish: convergence to positive information makes those events negligible.
The third-derivative envelope and two fixed-parameter LLNs control the entire
random segment. The sample criterion uses the average with divisor n; Wilks
multiplies its difference by 2n, whereas the estimator uses square-root n.
The target variances are I for the score and inverse I for the estimator,
and I times the squared limiting estimation error has χ²(1) law. All moment,
measurability, domain, and positive-information assumptions are explicit. The
input criterion is not itself required to be a normalized log density: each
statistical application must verify that interpretation and the information
identities. These are sufficient scalar conditions, not a proof of every
model covered by the notes' unspecified regularity language.

The constant-estimator admissibility proof uses nonnegative extended risk and
compares all measurable estimators. A competitor with risk at most zero at
θ = c must equal c almost surely at that parameter. Absolute continuity of
all normal sample laws transfers this equality to every parameter, precluding
strict improvement. Finite product absolute continuity is proved explicitly;
no restriction to affine competitors or finite-risk competitors is imposed.
Sample-mean and normal Bayes risks use the actual normal sample-mean law.

Wilson endpoint inversion retains both tails and assumes a positive sample
size and an observed mean in [0,1]. The bridge to the divided Bernoulli score
statistic requires the null parameter in (0,1), where its denominator is
positive. This algebraic equivalence does not assert exact finite-sample
coverage from an asymptotic critical value.

## Normal minimax and positive-part review

The normal-normal calculation retains both density normalizers. Its scalar
identity is multiplied over the finite coordinates, and Tonelli exchanges
prior and sampling integration for every nonnegative measurable loss. The
posterior law has mean `w/(v+w) y` and variance `v*w/(v+w)`, with `v` and `w`
denoting sampling and prior variances, not standard deviations or precisions.
The posterior loss at action `a` is exactly `p*v*w/(v+w)` plus the squared
distance from the posterior mean. This proves the Bayes lower bound without
assuming a competitor's risk is finite, or assuming that it is linear.
The posterior-mean rule attains the bound and is proved Bayes.

The minimax proof uses the proper priors with variance `w = v*(n+1)`. Their
Bayes lower bounds increase toward `p*v`, so every measurable rule has worst
risk at least `p*v`. The identity attains it. Both shrinkage rules inherit
minimaxity and their worst risks are proved equal to `p*v`. In particular,
strictly smaller pointwise risks do not imply a strictly smaller supremum.
The decision space for minimaxity is explicitly all measurable rules; it has
no boundedness, finite-risk, linearity, or equivariance restriction.

The positive-part proof does not apply a smooth Stein identity at the kink.
For a reflected pair `y,-y`, the sign of the difference between Gaussian
densities agrees with the sign of the inner product of the mean with `y`.
Expanding the two squared losses proves that truncating any negative,
reflection-invariant multiplier lowers their density-weighted sum. Nonnegative
integration and reflection invariance of Lebesgue measure give the risk
inequality, even for infinite risks. At the zero mean the inequality is strict
on `0 < sum(y_i^2) < (p-2)*v`; this is a nonempty open set with positive normal
probability. Thus the proved conclusion is dominance (weakly at every mean,
strictly at zero) and inadmissibility of James–Stein among measurable rules.
It does not claim the stronger, unnecessary assertion of strict positive-part
improvement at every mean. The estimator values at the origin are both zero.
All strict claims explicitly require `p ≥ 3` and `v > 0`.

## September 30: quantiles, calibration, and intervals

The quantile is the lower generalized inverse `inf {x | q ≤ F(x)}`. Its
theorems require `0 < q < 1`, ensuring a finite real endpoint. The proof uses
both tails of the CDF and its right continuity; it retains jumps through
`P(X < c) ≤ q ≤ P(X ≤ c)`. Exact calibration without randomization is asserted
only for atomless laws. Randomization at a boundary atom uses a coefficient in
`[0,1]` and exactly fills the gap between open and closed tails.

Neyman–Pearson existence handles zero null density explicitly: the rule
rejects there, including where the alternative density is positive. It does
not assume absolute continuity of the alternative with respect to the null.
The null density is normalized; comparison is proved against every measurable
randomized test of size at most the target. The alternative need only be
integrable and nonnegative for the mathematical comparison. When interpreted
as power under a probability model, it must also integrate to one.

The MLR proof retains common strictly positive densities. A cutoff need not
belong to the statistic's range: in that case a supremum of likelihood ratios
above the cutoff separates the two regions. Nontriviality follows from
interior-size calibration. Composite-null level and alternative optimality
are separate conclusions. The additional monotonicity theorem says
nonincreasing power; it does not inherit the notes' incorrect strict claim.

The normal formulas use variances, with standard deviation `sqrt v` and sample
mean standard error `sqrt (v/n)`. Exact two-sided power keeps both tails.
Student intervals require `n > 1`, positive population variance, and the
proved almost-sure positivity of sample variance. Variance intervals use
`(n-1)s²` and chi-square degrees of freedom `n-1`; quantile positivity is
proved before division. Chi-square atomlessness is proved by conditioning on
one normal coordinate, and Student atomlessness by conditioning on the
positive chi-square denominator. Arbitrary interior tail allocations include
equal and unequal tails. Gaussian credible content is measured under the
posterior Gaussian, separately from frequentist coverage.

Bootstrap quantile consistency uses conditional CDF convergence to a fixed,
atomless, strictly increasing CDF. Random cutoffs may depend on the same data
as the statistic: Slutsky and null-boundary convergence justify their use.
The interval theorem applies to the normalized estimation error and to the
conditional law of its normalized bootstrap analogue. For a consistent basic
estimator, the scale is a vanishing deterministic inverse rate; convergence of
both unscaled errors to zero would be insufficient. For studentization the
scale is the estimated standard error. Measurability of the statistic and
cutoffs and almost-sure positivity of the scale are explicit. The proof does
not establish model-specific conditional CLTs, higher-order refinements,
uniform-in-parameter coverage, or validity with a fixed number of Monte Carlo
replicates.

HPD cutoff existence assumes that density values have an atomless law under
the posterior. Positivity of the density almost surely under its own measure
is derived even when it vanishes on part of the reference space. An interior
quantile gives a positive cutoff, exact content, and minimum reference volume.
The October 2 additions below supply the separate plateau construction on
an atomless real parameter space and extend quantile reparameterization to
non-surjective increasing maps and decreasing maps with explicit CDF conditions.

## Exponential MLE example

The exponential parameter is a positive rate `r`, with mean `1/r` and
variance `1/r²`. The log-likelihood identity is established for the actual
normalized density on its nonnegative support. The derivative equation alone
is not used to assert a maximum: the logarithm inequality proves that
`n/sum(x)` globally maximizes the likelihood when `n > 0` and `sum(x) > 0`.
The latter condition holds almost surely under the model. At a zero sum no
finite rate maximizer is claimed.

The score has mean zero, second moment and variance `1/r²`, equal to minus the
expected Hessian. The sample-mean LLN and CLT follow from the IID exponential
law and its proved moments. Continuity at the positive mean gives MLE
consistency; an exact reciprocal identity and Slutsky give the rate MLE's
normal limit with variance `r²`. The almost-sure positivity proof justifies
division for each positive sample size, while the zero-sample index has zero
square-root scaling. Neither consistency nor estimator asymptotic normality
is assumed. The plug-in theorem estimates the variance of the scaled limit;
the unscaled estimator's asymptotic variance includes the additional `1/n`.


## Full logistic derivatives, vector Wald inference, and boundary normal estimation

The October 1 additions were checked against L7's logistic and boundary examples,
L7's information-estimation paragraph, L10's vector Wald discussion, and L11's
ellipse projection. Their precise scope is:

- `LogisticMultivariate` takes fixed covariates and Boolean outcomes. Its sample
  criterion is proved equal to the log of the product of the normalized Bernoulli
  masses. Both the criterion's Fréchet derivative and the score's derivative are
  identified, so the Hessian quadratic form is attached to the actual likelihood.
  The conditional score mean and information use the same Bernoulli probabilities.
- Concavity gives global optimality of every score root. The converse uses a
  local-maximum derivative theorem on the whole Euclidean parameter space. Full
  column rank is injectivity of the design map, which gives strict concavity,
  negative curvature in every nonzero direction, and uniqueness if a maximum
  exists. Complete separation strictly improves the likelihood along a fixed
  direction and hence prevents a finite maximum. Full rank alone does not assert
  existence. Random-design logistic asymptotic normality is not claimed here.
- `VectorWald` uses the ordinary finite matrix Borel structure and entrywise sup
  metric. A nonsingular limiting matrix justifies inverse consistency, even when
  finite-sample estimated matrices can be singular. The limiting Gaussian
  covariance is positive definite; the dimension must be positive for continuous
  chi-square quantile calibration. The estimator's Gaussian limit and consistency
  of the estimated covariance remain explicit inputs. No independence of these
  two estimates is assumed. The quadratic-form scaling identity explicitly
  connects normalized errors to the displayed `n * (estimate - truth)ᵀ S⁻¹
  (estimate - truth)` statistic and its ellipsoid coverage. Coverage is pointwise,
  not uniform over parameters.
- Plug-in information requires continuity at the parameter and nonsingularity
  there. Sandwich consistency requires consistency of both component matrices.
  The general formula is `H⁻¹ J (H⁻¹)ᵀ`; the transpose is redundant for symmetric
  Hessians, as in the notes. No law of large numbers for an arbitrary estimated
  score or Hessian is smuggled into this continuous-mapping result.
- `EllipseProjection` proves equality with the actual two-by-two inverse matrix
  quadratic form before completing the square. Positive marginal variance,
  positive determinant, positive sample-size scale, and a nonnegative cutoff are
  explicit. The two radii are `sqrt(q*a/N)` and `sqrt(q*b/N)`, where `q` is the
  joint cutoff. The minimizing other coordinate depends on the covariance. These
  are projection intervals, not a claim that two marginal 95% intervals provide
  95% simultaneous coverage.
- `BoundaryNormalMLE` compares actual products of unit-variance Gaussian
  densities over nonnegative means. The square-root limit at mean zero is derived
  from IID Gaussian observations and the continuous positive-part map. Its atom
  at zero is proved positive, ruling out every Gaussian with positive variance.
  This does not claim that the positive-part law is a truncated and renormalized
  normal distribution: mass on negative outcomes is placed at zero.


## Scalar misspecification, information estimation, and further examples

The October 2 additions were checked against L7's information estimation,
incidental-parameter and pseudo-MLE discussions, L9's normal testing examples,
and L12's HPD and quantile statements. Independent review checked the formal
hypotheses and conclusions in addition to compilation.

- `PseudoMLE` separates score variance `J` from negative mean curvature `H`.
  It derives the score CLT, curvature and envelope LLNs, and the interior
  first-order equation, obtaining limiting variance `J/H²`. Positive `H`,
  zero mean score, moments, derivatives, consistency, and measurable interior
  maximizers are explicit. It is scalar, and does not prove consistency for an
  arbitrary misspecified model. The log-ratio identity requires positive
  densities almost everywhere and integrable logarithms under the true law;
  it does not assert a general identity for infinite relative entropies.
- `InformationEstimation` proves convergence of an average evaluated at a
  consistent random parameter from a local Lipschitz bound with an integrable
  envelope. Joint measurability and a separate composition theorem ensure that
  the estimated statistic is measurable, beyond the outer-measure bounds used
  in the convergence proof. Applying the mean-value bound to a third derivative
  gives observed negative-curvature consistency. Its limit is the negative
  expected curvature; equality with score variance is not assumed under
  misspecification. Verification of the envelope remains model specific.
- `NeymanScott` uses independent normal pairs, independent coordinates within
  each pair, a common variance, and unrestricted means that may vary with the
  pair index. Differences eliminate the nuisance means and have a common
  centered Gaussian law. The likelihood variance estimate is the sum of
  squared differences divided by `4n`, converges to `v/2`, and is inconsistent
  for positive `v`; doubling it is consistent. The actual joint product
  density is maximized by the pair means and this variance when the residual
  is positive, which occurs almost surely for a nonempty nondegenerate sample.
  At zero residual no positive variance maximizes the likelihood.
- `HighestDensityPlateaus` includes all points strictly above the cutoff and
  enough of the equality region to attain exact content. An atomless finite
  real measure can split a measurable set to any mass; this is proved using a
  quantile of its normalized restriction. The posterior cutoff is positive at
  interior levels, and minimum reference volume holds even against competitors
  of infinite volume. Neither uniqueness nor an interval shape is claimed.
  Exact set existence is restricted to real parameters with an atomless
  reference measure, since arbitrary atomic parameter spaces cannot generally
  realize a prescribed mass without randomization.
- `QuantileReparameterization` fixes the lower generalized-inverse convention.
  Continuous strictly increasing maps preserve the quantile and interval
  endpoints, including for atoms and non-surjective maps such as exponentiation.
  Decreasing maps exchange the tail levels and endpoint order. The proved
  decreasing result assumes an atomless input law with a globally strictly
  increasing CDF. This sufficient condition excludes bounded-support laws and
  avoids ambiguity from CDF plateaus. The source's unqualified monotone
  invariance statement is not silently asserted for every discrete distribution
  or arbitrary choice of generalized-inverse endpoints.
- `NormalLikelihoodRatio` uses the ratio of suprema of the actual unit-variance
  Gaussian product density. For positive sample size its unique unrestricted
  maximizer is the sample mean and `-2 log LR = n (mean - null)²`; the chi-square
  null law and quantile calibration are exact. The empty sample has ratio one.
  `NormalUMPNonexistence` treats every measurable randomized test of one normal
  observation with positive known variance. Neyman–Pearson equality forces the
  lower-tail rule against a smaller mean. Against a larger mean this rule has
  power below its null size and is beaten by constant randomization, proving
  nonexistence of a two-sided UMP rule. The single-observation experiment also
  describes tests observing only a normal sample mean; no reduction of all
  full-sample tests to that experiment is claimed.

- `NormalHighestDensity` proves Gaussian quantile symmetry and identifies a
  central interval as an actual density superlevel set. Its equal-tailed interval
  has exact posterior content and minimizes Lebesgue volume among all measurable
  competitors, including disconnected sets, with no uniqueness assertion.
- `EstimatedInformationIntervals` proves pointwise frequentist coverage from a
  Gaussian sampling limit with variance `I⁻¹` and a consistent estimated
  information `J`. Each finite-sample `J` must be positive almost surely; this is
  an extra hypothesis, not a consequence of consistency alone. Index `n`
  represents sample size `n+1`, so the endpoints use `sqrt(1/((n+1)J))`.
  The studentized limit and interval inversion are derived, with no independence
  assumption. The unequal-tail result specializes to the displayed equal-tailed
  interval by proved normal quantile symmetry. Sampling coverage is separate
  from posterior probability, and the inverse-information sampling variance
  must be established; misspecified models do not automatically satisfy it.

- `PosteriorInformationIntervals` controls moving events using the existing
  uniform posterior approximation, then proves Gaussian probability convergence
  for the changing width. This yields posterior content `1−α` for the same
  estimated-information interval and an almost-sure pathwise version. It
  requires positive estimated information at each sample size. The normal-mean
  kernel corollary derives posterior approximation from bounded continuous
  integrable priors positive at the truth and supplied center consistency;
  it does not assume the posterior approximation itself, nor does this module
  derive center consistency from IID observations. This transfer step is not a
  general vector or misspecified-model Bernstein–von Mises theorem.

- `UniformEndpoint` fixes the density version `1_[0,θ]/θ` for `θ>0`;
  including the upper endpoint makes a positive observed maximum attain the
  likelihood. The normalized Lebesgue restriction and this density are proved
  to define the same law. With `N=n+1` independent observations, the maximum
  divided by `θ` has the actual `Beta(N,1)` law. Its mean is `θN/(N+1)`,
  variance is `θ²N/((N+1)²(N+2))`, and mean squared error is
  `2θ²/((N+1)(N+2))`. These formulas yield consistency and convergence of
  `sqrt(N)(maximum−θ)` to zero in probability. The last result is a degenerate
  centered Gaussian limit; the source's informal exclusion of a mean-zero
  Gaussian must be understood as excluding a nondegenerate one. The likelihood
  for an empty sample is constant one. A positive maximum is required for the
  positive-parameter maximizer statement; support and positivity hold almost
  surely under the uniform model, and the theorem is applied on that event.
  For a nonempty all-zero sample, halving any positive endpoint strictly
  improves its likelihood, so no positive endpoint maximizes it.
