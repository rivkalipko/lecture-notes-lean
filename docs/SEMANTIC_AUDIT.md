# Semantic audit of the formal statements

Audit date: 2026-09-13. Starting revision: `2c5ec26724c924547fd45b501c889f04a09b8576`.

The review covered definitions, theorem statements, and proof arguments in
all 31 modules present at that revision. It compared the mathematical objects,
quantifiers, hypotheses, and conclusions with the corresponding passages in
the six source PDFs. `BernoulliModel` was added as a concrete check of the
density and score definitions. That reviewed snapshot had 32 modules; later
additions and current verification results are recorded below.

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
| `Foundations`, `ProbabilityLaws`, `ConditionalExpectation` | Event products, intersections and complements; conditional-probability direction and denominators; CDF endpoints and right continuity; L1/L2 hypotheses; almost-everywhere equalities; conditional squared-loss orthogonality. The initial real-risk result required square-integrable competitors; ConditionalPrediction subsequently removed that restriction using extended risks. |
| `Sampling`, `SamplingMoments`, `FinitePopulation` | Mean denominator `n`, sample-variance denominator `(n : Real) - 1`; positivity of sample/population sizes; off-diagonal and diagonal covariance terms; HT population-mean normalization `1/N`; actual uniform-subset design and inclusion probabilities; finite-population correction, including one draw and the census case. |
| `NormalSampling`, `NormalSamplingDistribution`, `GaussianQuadraticForms`, `GaussianMahalanobis`, `NormalFStatistic`, `ChiSquaredMoments`, `NormalVarianceRisk` | Independence is joint where needed; mean variance is `v/n`; residual rank and t degrees of freedom are `n-1`; nonzero random denominators follow almost surely; F statistic includes the population-variance ratio; matrix projections require symmetry and idempotence; Mahalanobis covariance is positive definite; fourth normal moment is proved, not assumed; `v^2` denotes the notes' fourth power of the standard deviation. |
| `Inequalities`, `Concentration` | Hölder absolute values and conjugate exponents; Markov/Chebyshev thresholds; Hoeffding exponent and interval width; independent bounded observations. The subgaussian auxiliary bound at zero variance proxy is only its totalized, possibly uninformative extension; the statistical Hoeffding formulas require positive interval width and sample size. |
| `LargeSample`, `Convergence`, `WeakLaw`, `CramerWold`, `MultivariateCLT`, `DeltaMethod`, `StochasticOrder` | Centering, square-root scaling, finite moments, common versus separate probability spaces, all five convergence implications, Slutsky division limit, every linear projection in Cramér–Wold, transformed delta-method variance, measurability of the divided difference, and uniform-in-n stochastic-order quantifiers. The multivariate CLT specifies the target through Gaussian projection laws; it does not construct a target from a covariance matrix. The CDF equivalence bridge was subsequently completed in `CDFConvergence`. |
| `EmpiricalDistribution`, `Bootstrap` | The CDF uses `<=`; indicator expectation and variance are actual probabilities; consistency and concentration quantify over a fixed threshold. The separate uniform DKW and Glivenko–Cantelli results were subsequently completed; see the coverage ledger. Bootstrap samples use independent indices drawn with replacement from the uniform index law. |
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

At this initial audit snapshot, Lindeberg–Feller, Glivenko–Cantelli/DKW,
general density factorization, distribution transformations and several
examples were still pending. They were subsequently completed as detailed
in the dated additions below and the current coverage ledger. The unrestricted
pointwise minimal-sufficiency criterion is false; its counterexample and valid
almost-everywhere scope are recorded there. Some included proofs apply Mathlib
results instead of reproducing the lecture proof line by line. No claim of
complete transcription follows from this historical audit.
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

## October 2 continuation: probability foundations

- `VectorScoreCLT` constructs the covariance matrix from actual coordinate
  covariances, proves positive semidefiniteness, and matches all scalar
  projection variances of its Gaussian law. The CLT now has a canonical target
  without an extra existence assumption. Singular covariance and dimension
  zero are allowed; the linear transformation law uses `A S Aᵀ`. Its score
  specialization uses the actual square-root-times-average statistic, and
  centering is justified by an explicit zero-mean hypothesis.
- `CDFConvergence` proves both directions of the lecture's CDF definition of
  convergence in distribution. Only continuity points of the limiting CDF
  are needed. Continuity at a point implies zero singleton mass, and half-open
  intervals with continuity-point endpoints form a convergence-determining
  family. The random-variable statement concerns the actual pushforward laws
  and probabilities, allowing different sample spaces and atoms.
- `EmpiricalUniform` proves all-real uniform empirical-CDF convergence for
  arbitrary IID observation laws. Its countable common probability-one event
  contains convergence of both strict and weak lower-tail empirical counts at
  quantile partition points. This is essential for atoms. The resulting
  uniform and supremum conclusions are stronger than the earlier pointwise
  theorem. The partition bound has a mesh error and is not presented as the
  sharp DKW inequality.
- `EmpiricalSupMeasurable` reduces the real supremum to rational thresholds
  using right continuity, approaching from above so atoms cause no gap.
  The supremum is bounded by one and measurable. The empty-sample case is
  separately justified before applying the empirical probability law.
- `LindebergAnalytic`, `LindebergBounds`, and `LindebergFeller` prove the
  non-identically distributed CLT. The characteristic-function remainder has
  a cubic bound on small observations and a quadratic bound on the tail;
  only second moments and the actual Lindeberg tail condition are required.
  Replacement by Gaussian factors proves convergence of the whole product.
  Individual normalized variances vanish and their squared sum tends to zero.
  The source sequence theorem centers at each actual expectation, takes
  `c_n² = sum variance`, and explicitly requires eventual `c_n > 0`.
  `Lyapunov` proves both the normalized-row and original-sequence sufficient
  conditions, for every positive real exponent increment, then derives their
  CLTs. Higher-moment integrability is explicit.

## October 2 continuation: statistical experiments and vector limits

- `DominatedSufficiency` relates the common conditional-law kernel to
  Radon–Nikodym factorization. `MixtureSufficiency` preserves that kernel under
  countable mixtures. `DominatingMixture` constructs a finite dominating
  mixture of model members from sigma-finite domination, rather than assuming
  a dominating member exists. `FisherNeymanGeneral` proves the full density
  factorization equivalence on nonempty standard Borel sample spaces. Density
  equality is reference-almost-everywhere for every parameter. The carrier
  can vanish and need not have a finite integral. The intermediate finite
  carrier theorem is a useful normal form, not a restriction of the final
  theorem. An infinite-valued carrier is trimmed only where every model
  density vanishes almost everywhere, as justified in the proof.
- `ExponentialFamilySufficiency` starts with normalized single-observation
  densities and proves the actual product law has their product density.
  It factors through all canonical sums and derives sufficiency; there is no
  finite-support assumption or unproved conditional-density-on-a-fiber step.
- `IsMinimalSufficientStatistic` means that every sufficient standard Borel
  reduction determines the proposed statistic through one measurable map,
  valid almost surely under each model law. Finite or countable likelihood
  ratios plus an explicit measurable decoder prove this property. A finite
  dominating mixture handles varying supports. This is not yet the source's
  completely general pointwise ratio-equivalence criterion.
- `NormalSufficiency` treats the entire product experiment, not merely the
  experiment observing the mean. The Gaussian density ratio factors through
  the sum; a nonzero mean contrast recovers the mean, proving minimality.
  Known variance and sample size are positive. `UniformSufficiency` allows
  parameter-dependent support: the maximum is sufficient for the unbounded
  positive endpoint family, and both extremes are sufficient for the location
  of a unit interval. These statements use actual product measures.
- `VectorScoreAsymptotics` derives an exact linear score identity using a
  measurable rank-one correction and bounds it by the derivative envelope.
  It avoids selecting random mean-value points. Consistency and the curvature
  LLN make that operator converge to the limiting curvature. Inverses only
  need to exist with probability tending to one; singular finite-sample
  operators are controlled through the shrinking exceptional event.
- `VectorMLE` derives the score CLT, derivative and envelope LLNs, and interior
  first-order equation from IID observations. Separate score covariance and
  negative expected curvature produce the sandwich covariance. Equating the
  covariance operator with the curvature gives the inverse-information limit.
  Consistency and measurable interior maximization remain explicit hypotheses;
  normalization and information identities are model obligations.
- `BootstrapMoments` identifies all integrals against the empirical law as
  finite sample averages. Under the actual IID resampling law, the bootstrap
  mean has mean equal to the observed mean and variance equal to the empirical
  variance divided by sample size. The empirical variance uses denominator n.
  Strong consistency follows from LLNs for X and X²; no fourth moment is
  imposed. These moment results do not assert a conditional bootstrap CLT.
- `NormalUnknownVarianceMLE` proves global maximization of the actual normal
  product density at the sample mean and empirical variance when that variance
  is positive. At zero empirical variance, fitting the mean and halving any
  positive candidate variance strictly improves the likelihood. For more than
  one independent normal observation with positive population variance, the
  exceptional zero-variance sample is proved null.

- `DKWAnalytic` proves the Bernoulli relative-entropy bound
  `D(p‖q) ≥ 2(p−q)²`, including p=0 and p=1 by continuity, with
  q strictly between zero and one. This analytic component is used in the completed DKW proof described below.

- `VectorWilks` proves a deterministic quadratic remainder bound from actual
  criterion/score derivatives and a Lipschitz derivative envelope. Tightness
  of the normalized error and vanishing curvature error make the scaled
  remainder negligible. Both fixed and random null points are treated.
  `ConstrainedVectorMLE` derives the full/restricted joint root limit from the
  same score process, retaining their dependence. Its final linear-subspace
  theorem uses the actual projected full gradient at every subspace point,
  derives curvature control at the moving restricted estimate, and proves
  the chi-square law with degrees of freedom equal to codimension. Neither
  a joint estimator limit nor a likelihood expansion is a premise of that
  final theorem. The coordinates have identity limiting information, the
  true parameter is zero, and both roots are consistent and stationary.
  This does not yet prove the source's general nonlinear-restriction claim.

- `LikelihoodRatioSupport` identifies the zero sets of model densities with
  the zero sets of their Radon–Nikodym ratios under a dominating reference.
  `UniformEndpointMinimal` then recovers the maximum from the countable
  positive rational upper cut, using a proved measurable extended-real
  infimum decoder. All observations and the maximum are positive almost
  surely under the experiment and under its dominating mixture. The result
  covers the whole unbounded positive endpoint family, without supposing
  that one model member dominates every other member.


## October 2 continuation: sample variance and further posterior/examples

- `VarianceAsymptotics` proves L5 Examples 7 and 8 for the actual sample
  variance with denominator n−1. Its exact finite-sample decomposition reduces
  the centered empirical variance to an average of squared centered observations
  and a negligible squared sample-mean error. Second moments suffice for strong
  consistency; the CLT explicitly requires a finite fourth central moment.
  Its target variance is proved equal to the fourth central moment minus squared
  population variance, including a zero limiting variance. The deterministic
  correction for denominator n−1 is derived, and n=0/1 are excluded only
  eventually. Independent review against both source examples found no
  normalization or hypothesis gap.
- `RationalIntervalDecode` supplies a common measurable decoder of an interval
  from countably many rational membership indicators. `UniformLocationMinimal`
  uses it to recover both sample extremes from likelihood-support information.
  The sample range is strictly less than one almost surely under every
  translated-uniform model and under the dominating mixture. This avoids the
  source's undefined all-zero likelihood ratios for impossible samples.
- `TriangularSufficiency` constructs the normalized strict-support density
  2x/θ² on (0,θ), proves its IID product factorization, and establishes maximum
  sufficiency. `TriangularEndpointMinimal` uses strict rational upper cuts to
  prove minimality for this same experiment; it does not substitute a uniform
  density or change the source's endpoint convention.
- `VectorGaussianKernel`, `VectorPosteriorAsymptotics`, and
  `VectorNormalPosteriorLimit` extend the scalar posterior argument to Euclidean
  parameters. The target Gaussian has covariance A Aᵀ for any invertible scale
  factor A, without assuming A is symmetric. The dimension-power scaling and
  absolute determinant in the affine Jacobian are proved for the actual
  posterior pushforward. Local quadratic convergence, prior continuity and
  positivity, and a global integrable envelope imply a uniform bound over all
  measurable events tending to zero. The normal-mean model verifies the
  envelope and evidence conditions for bounded continuous integrable priors.
  Independent review checked covariance orientation, Jacobians, normalization,
  and that the target posterior approximation is derived rather than assumed.

- `VectorNormalSamplePosterior` connects the quadratic kernel to the actual
  normalized multivariate Gaussian density, proves the product-likelihood
  centering identity, and derives almost-sure posterior approximation under
  IID sampling. The strong law supplies center consistency; it is not a
  premise of the final IID theorem. Its scaling is √(n+1) for samples of size
  n+1. The sample average also globally maximizes the actual density product.
  A second reviewer checked this connection independently.
- `LindebergRows` allows each triangular-array row its own measurable sample
  space and probability law. The proof remains row-local: characteristic
  functions factor within a row, and only the stated variance normalization
  and Lindeberg tails connect the rows. The conclusion uses Mathlib's actual
  dependent-space distributional convergence. This permits the empirical
  resampling law to change with sample size without a fictitious fixed law.

- The completed sharp DKW proof now spans `DKWCensorBridge`, `DKWMaximal`,
  `DKWGrid`, `DKWQuasiconcavity`, `DKWEvents`, `DKWUniform`,
  `DKWQuantileCoupling`, and `DKW`. The conditional-expectation identity is
  proved for actual IID uniform observations by finite tilted measures and
  censoring; reversing threshold order gives the filtration. Doob's inequality
  controls all finite-grid crossings at once. Quasiconcavity, quasiconvexity,
  the Bernoulli entropy bound, and Sion's theorem provide a common tilt with
  an arbitrarily small slack; taking the slack to zero gives the exact rate.
  Integer count witnesses replace the continuum by finitely many thresholds.
  Reflection handles lower tails without discarding ties. The generalized
  inverse transports the entire product law and bounds the actual supremum
  event for arbitrary laws, with no atomlessness assumption on the data.
  Independent review checked the full assembled statements and rate. The
  PDF's absolute-value bars are present: the extracted text loses them, as
  recorded by the earlier visual source audit. The lower-deviation theorem
  is an additional corollary of the main two-sided source statement.

- `MethodOfMoments` derives scalar inverse-moment consistency from the IID
  strong law and its asymptotic law from the actual IID CLT and delta method.
  The inverse is continuous and differentiable as explicitly stated, and
  identification at the population moment is required. A zero inverse
  derivative is allowed. The normal moment equations yield the empirical
  variance with denominator n; exponential alternatives identify positive
  rates from their actual first and second moments. These do not assert
  generic multivariate inverse-moment asymptotics.
- `InstrumentalVariables` starts from the residual Y−α−βD, zero mean, zero
  instrument covariance, and nonzero covariance between instrument and D.
  It derives the displayed population ratios and proves that their empirical
  counterparts uniquely solve the sample equations. Strong covariance and
  slope consistency use L² coordinates, allowing dependence within a draw.
  No causal interpretation is inferred beyond the supplied moment conditions.
- `UnbiasedNonexistence` proves L5 Example 2 for the actual product Bernoulli
  experiment, allowing every real-valued estimator on the finite sample
  space. The expectation is bounded uniformly across parameter values,
  whereas 1/p is unbounded near zero. This is a different valid proof from
  the source's polynomial argument. Independent review matched all three
  modules above to the directly read L5/L6 source passages.

- `GumbelSufficiency` normalizes the actual Gumbel location density and derives
  sufficiency and minimality of the sum of exp(−X). `CauchyPolynomial` and
  `CauchySufficiency` recover the full sorted Cauchy location sample from a
  countable likelihood-ratio representation. Complex roots retain repeated
  observations and their multiplicities. `BinomialTwoSufficiency` uses the
  actual three-point Binomial(2,p) law on the full closed parameter interval;
  the endpoints are not removed by the positive-density reference used for
  minimality. Its normalizer and finite-product factorization are proved.
- `UniformCDFConvergence` proves uniform convergence of real-line CDFs from
  pointwise convergence to an atomless limiting law. The approximating laws
  may have atoms, and the limit may have flat portions. `RowStudentization`
  proves CDF convergence after division by a scale tending to one in its
  row probability, with sample spaces and laws allowed to vary by row.
  Zero or negative scales lie in a vanishing bad event. An independent
  review checked the signs of both CDF bounds and these scope conditions.
- `Correlation` proves the covariance equality characterization by almost-sure
  affine dependence and the absolute-correlation characterization under
  positive variances. Its finite-second-moment and nondegeneracy assumptions
  are explicit. Independent review matched the statement to L1.
- `BootstrapLindeberg` derives the actual centered empirical Lindeberg tails
  from a finite second moment, using truncated strong laws.
  `BootstrapConditionalCLT` then obtains the conditional sample-mean CLT
  under the actual resampling law, with a law that changes with sample size.
  `BootstrapMeanIntervals` derives basic interval coverage with reversed
  conditional-quantile endpoints and no independence of endpoints and data.
  Positive population variance is required; the conditional quantile limit
  and its measurability are proved. Independent review checked this entire
  composition against the bootstrap and confidence-interval passages.

- `BootstrapVarianceMoments` and `BootstrapVarianceConsistency` derive the
  resampled variance and scale consistency from actual conditional moment
  bounds and the original-sample strong law. `BootstrapStudentizedLaw`,
  `BootstrapStudentizedAsymptotics`, and `BootstrapStudentizedIntervals`
  retain the actual statistic and quantiles even when finite-sample variances
  vanish. Such cases lie in events proved to have probability tending to zero.
  The final bootstrap-t interval theorem uses finite fourth moments, positive
  population variance and exact conditional quantiles; it derives nominal
  coverage b−a. Independent review checked tail orientation, the n+1 scaling,
  both zero-variance exceptions, and that no limit conclusion is a premise.
- `EmpiricalQuantiles` proves sorting preserves empirical laws and identifies
  the exact ceiling-rank quantile, retaining observation multiplicities.
  `BinaryInstrument` proves covariance factorization by the two empirical
  group proportions and derives the group-means ratio and relevance criterion.
  Independent review checked both modules against L2/L4 and L6 respectively.
  The ratio equality alone uses total real division; its statistical use
  additionally requires the separately characterized nonzero first stage.

- `MonteCarlo` derives the IID pushforward law of a separately applied
  statistic, then proves simulation consistency for integrable means, fixed
  measurable-event probabilities, square-integrable sample variances, and
  empirical quantiles under the stated crossing condition. Atoms and bounded
  supports are allowed; a flat CDF at the selected level may prevent quantile
  convergence. Independent review checked these conditions and the nonempty
  empirical-law indexing. Simulation error is distinct from replacing the
  unknown population by an estimated law.
- `GaussianConditioning` derives an actual regular conditional law from an
  independent Gaussian regression residual. Its scalar conditioning variance
  is positive, while the Schur-complement residual variance may vanish. The
  formula holds almost everywhere under the conditioning variable's marginal
  law, as a regular conditional-distribution formula should. Independent
  review checked the affine mean, variance subtraction and conditional-law
  orientation.

## Further source-to-statement review on October 2

The following modules were reviewed independently of their implementation.

- `GaussianBlockConditioning` uses the rectangular cross-covariance and the
  actual Schur complement. The conditioning covariance is positive definite;
  the residual covariance may be singular. Conditional-law equalities are
  marginal-almost-everywhere. `GaussianRadialMoments`, `StudentTMoments` and
  `StudentTIntegrability` prove that Student-t is integrable exactly for n>1
  and square-integrable exactly for n>2. Its mean is zero for n>1 and variance
  n/(n−2) for n>2. For the other positive degrees of freedom, divergence is
  stated using the nonnegative extended integral, not an infinite real variance.
- `BernoulliBinomialMoments` and `PoissonMoments` connect MGFs and moments to
  their actual probability laws, including p=0, p=1, zero binomial size and
  zero Poisson rate. `UniformSquare` proves the actual square pushforward of
  Uniform[0,1], its clipped-square-root CDF, Beta(1/2,1) law and density.
  `DensityTransform` proves equality of actual pushforward density measures.
  The reciprocal Jacobian version requires nonzero derivative, with a separate
  source/target-set formulation for transformations with proper ranges.
- `BinomialSample`, `BinomialConditioning`, `BinomialRaoBlackwell` and
  `BinomialMinimal` cover L5 Example 19 for general Binomial(k,p) observations.
  The estimator of P(X=1) is parameter independent. Conditional formulas are
  asserted at positive-mass totals, and the estimator is zero beyond feasible
  totals. Its factorial expression is restricted to its valid factorial range.
  Risk reduction, unbiasedness, sufficiency and minimality use the actual
  finite product model, retaining p=0 and p=1.
- `WeightedEstimators` derives the actual weighted-estimator MSE before
  optimizing it. Unbiasedness at a fixed zero mean does not require unit-sum
  weights; unique minimum variance requires positive variance. The unrestricted
  MSE minimizer is an oracle depending on the unknown mean and variance. At
  mean zero its shrinkage coefficient equals one, rather than lying strictly
  inside (0,1). `ShrinkageImprovement` proves the exact pointwise improving
  interval and retains the variance positivity needed for strict improvement.
- `RandomizedExperiment` uses one actual uniform fixed-size assignment and
  its complementary control group. Observed-outcome equivalence and exact
  design-unbiasedness of the difference in means are proved without asserting
  independence between the two group averages. `Skewness` uses the source's
  n−1 sample variance in its denominator and includes the resulting n/(n−1)
  factor in the raw-moment formula.
- `CausalIdentification` derives the conditional-product identity from actual
  conditional independence through Mathlib's conditional distribution kernel.
  Conditional group means are observable ratios E[Y I(D=b)|X]/P(D=b|X).
  Positive overlap and observed/potential-outcome consistency are explicit;
  integrability of the final contrast and the total-expectation step are proved.
  `VectorDeltaMethod` and `VectorMethodOfMoments` derive the vector inverse-
  moment Gaussian limit from actual IID observations and a differentiable
  continuous inverse, with covariance AΣAᵀ and singular limits allowed.
- `PowerAnalysis` and `NormalSamplePower` retain both normal tails. The
  quantile sample-size/MDE expression is a sufficient power guarantee,
  not an exact inversion of the two-sided power function. The normal sample
  statistic's alternative law is derived from the actual IID Gaussian model.
- `SufficientTests` preserves power at every parameter when averaging any
  randomized test through the common sufficient kernel. `NormalFullSampleUMP`
  therefore proves one-sided UMP and two-sided UMP nonexistence for the full
  sample. `NormalPowerDerivative` derives the derivative under the Gaussian
  integral for every measurable [0,1]-valued test. `NormalUnbiasedNP` and
  `NormalUMPU` use its zero-score implication and a generalized NP comparison
  to prove the two-sided UMPU result against all unbiased randomized tests.
- `MLRNonnegative` removes the earlier common-positive-support restriction.
  Pointwise cross-product MLR, nonnegative integrable normalized densities and
  interior test size suffice for exact lower-tail randomization and UMP.
  Power is nonincreasing, including changing supports; strictness is not claimed.
- `CurvedWilks` uses the actual adjoint derivative of the chart to form the
  restricted likelihood score. The common score CLT and derivative envelopes
  yield both the joint estimator limit and LR expansion. The local chart is
  supplied, and information has been standardized to identity coordinates.
  Full rank of the restriction derivative determines the codimension; mere
  set-theoretic nonredundancy does not establish that rank or chart existence.
- `StochasticPowers` uses n+1 to match the lecture's indexing from one. Its
  positive-variance qualification is needed for nonzero SD normalization.
  Chebyshev's explicit constant gives ε/2<ε uniformly in n. Gaussian
  growing-variance examples concern marginal laws and assume no independence
  between different sample sizes.

- `BootstrapMaximum` proves that the conditional bootstrap maximum has an
  atom of at least one half at the observed maximum, uniformly in sample
  size and even with ties. The actual uniform endpoint error is strictly
  positive almost surely. Their gap-root CDFs therefore differ by at least
  one half at zero for every nonempty sample, a direct failure of bootstrap
  CDF approximation. Independent review checked both the resampling event
  and the actual uniform sampling measure.
- `AlternatingUniform` uses an actual Uniform[0,1] observation and its shift
  by −1 on odd indices. It proves uniform stochastic boundedness and rules
  out any weak limit by incompatible even/odd subsequences. On (0,1), the
  two CDF values are x and 1; the source's claim that they alternate between
  zero and a positive value is only correct on (−1,0).

- `StochasticSampleMean` proves the n+1 sample-mean stochastic rate from actual
  common moments and within-row pairwise independence. Its Chebyshev constant
  remains positive when population variance is zero; no across-row independence
  or additional distributional assumption is imposed. Independent review passed.

The complete 199-module snapshot passed the source scan, 8906-job build and
transitive proof audit: 2656 declarations, including 2347 theorem declarations,
with no prohibited axiom dependencies. Verification-copy parity covered 206
proof/audit/dependency files (173 unchanged Git hashes and 33 changed/new byte
comparisons). These figures certify the included snapshot, not full coverage.


## Further distribution and inference review (2026-10-02)

- `JointDistributions`, `ConditionalDensities`, `ConditionalDensityLaws`, and
  `DensityDerivatives` connect joint CDFs, marginals, density ratios and mixed
  derivatives to actual measures. Conditional density identities hold under
  the actual conditioning marginal almost everywhere; positive finite marginal
  density is derived there. The mixed derivative has sufficient continuity and
  integrable domination assumptions, rather than relying on CDF continuity.
- `PValues` and `PValueAsymptotics` prove exact upper-tail calibration for
  atomless laws, allowing flat CDF portions. The normal two-sided formula has
  the actual uniform law, including endpoints; its asymptotic calibration is
  tied to the finite-second-moment sample t statistic in `MeanTests`.
- `TwoSampleLindeberg`, `TwoSampleMeanCLT`, and `TwoSampleWelch` derive the
  unequal-variance two-sample pivot under finite second moments, with both
  sample sizes diverging and no assumed limit for their ratio. The estimated
  standard error uses denominator n−1 variances. Finite zero estimated standard
  errors do not invalidate the proved asymptotic result.
- `GaussianVarianceTests` uses the actual normal variance pivot with n−1
  degrees of freedom, an unrestricted unknown mean, and the correct lower-tail
  rejection direction. Its power is antitone in the true positive variance.
- `BootstrapVarianceLaw`, `RowPerturbation`, `BootstrapVarianceAsymptotics`, and
  `BootstrapVarianceIntervals` derive the actual conditional sample-variance
  law, uniform CDF and quantile convergence, and basic interval/test calibration.
  Finite fourth moments and positive variance of squared centered observations
  suffice. A second-moment resampling remainder estimate avoids imposing an
  eighth moment. The n−1 correction, measurable quantiles and exact cancellation
  of the unknown positive scale are proved. These are exact conditional
  quantiles; a fixed Monte Carlo budget is not treated as exact.
- `LinearContrasts` and `PretrendTests` derive rectangular covariance AΣAᵀ,
  the transformed Gaussian law, the exact placebo difference-in-differences
  formula and null equivalence, and the joint Wald calibration from a joint
  mean-vector CLT. No independence between periods is assumed. Only the final
  contrast covariance must be positive definite for ordinary inverse Wald
  calibration; singular input covariance is allowed.
- `HighestDensityNoninvariance` gives an actual Beta(2,1) posterior and a
  strictly increasing cube reparameterization. Its original HPD region has
  minimum volume and content 16/25. The transformed region has length 98/125,
  while a competing region with the same transformed content has length 64/125.

The complete 224-module snapshot passed the source scan, 8931-job build and
transitive proof audit: 2918 declarations, including 2588 theorem declarations,
with no prohibited dependencies. Verification-copy parity covered 231 files:
205 unchanged Git object hashes and 26 changed/new byte comparisons.
Independent review also passed for `IndependentLimits`,
`GaussianIndependentContrasts`, `VectorSampleMeans`, `TwoSampleVectorCLT`,
`CovariateBalance` and `MeanVarianceAsymptotics`. The actual allocation covariance,
total-sample-size Wald scaling, singular joint mean/variance limit, and positive
influence variance qualification for standardization were checked explicitly.
These checks certify the included snapshot, not all remaining source material.


## Sampling, nonlinear bootstrap and constrained-score review (2026-10-02)

- The convolution density retains extended values on null sets, and the
  shifted lognormal density equals the actual transformed Gaussian measure.
  Positive latent variance is needed for a density rather than a point mass.
- Survey sampling uses actual independent Bernoulli inclusion indicators.
  Unbiased estimation of the general pair terms requires positive pair
  inclusion probabilities; marginal positivity alone is insufficient.
- The normal and regression sufficient pairs factor actual normalized product
  densities. No design rank is needed for regression sufficiency. The negative
  unknown-variance assertion uses n>1 and follows from an independent-statistic
  law obstruction in a dominated model, not from informal density conditioning.
- The pointwise minimality counterexample leaves every model law unchanged,
  modifies a positive density only at one null point, and proves both the
  pointwise ratio criterion and failure of pointwise recovery. It is compatible
  with all correctly qualified almost-sure minimality statements.
- Smooth mean/variance bootstrap results use the actual n−1 sample variance,
  centered influence function, strict derivative and positive influence
  variance. The fourth-moment assumption controls the necessary quadratic
  remainders. The C² wrapper uses the actual Fréchet derivative. Independent
  review checked the conditional laws, quantiles, scale cancellation and
  rejection/coverage complements.
- Monte Carlo quantiles use ceiling ranks, include ties and have a proved DKW
  error bound. Actual P×Qₙ^B(n) laws represent data and independent simulation
  seeds; dominated convergence integrates the pathwise conditional result.
  B(n)→∞ suffices for first-order calibration. No across-row independence or
  critical-value independence from the data is assumed.
- ROC frontier proofs include budgets 0 and 1, treating null-density-zero
  regions explicitly. The targeting budget uses the population mixture,
  with positive prevalence specified where posterior rankings require it.
- Linear and curved score tests derive the ambient restricted score from
  effective curvature identities and the joint root limit under the common
  score CLT. They do not assume a projected-score limit. The curved chart,
  identity-information coordinates and consistency are explicit. Estimated
  inverse information converges and positive codimension permits quantile
  calibration. Independent semantic review passed all three modules.
- The Poisson numerical comparison uses finite logarithm-series bounds with
  a proved remainder; all decisions concern asymptotic reference rules. The
  chi-square-one CDF formula establishes strict reference p-value ordering.
- The Wald formulation counterexample has a regular null derivative and
  uses the gradient at the estimate in its plug-in covariance. The LR
  equality depends on literal equality of the two null sets.

- Independent review of `NormalVarianceTestOrdering` checked the actual
  positive-variance Gaussian log density, its score and expected curvature,
  global maximization at x², and the strict reversed ordering at x=√2.
  The mean is known, so the one-observation variance model has no unidentified
  nuisance parameter.

The complete 250-module snapshot passed the source scan, 8957-job build and
transitive proof audit: 3240 declarations, including 2873 theorem declarations,
with no prohibited dependencies. Verification-copy parity covered 257 files:
230 unchanged Git object hashes and 27 changed/new byte comparisons. The
26 added modules contain 161 source theorem declarations, 31 definitions and
7 instances. These checks certify this snapshot, not all remaining material.


## Model-specific inference and bias review (2026-10-02)

Independent review checked the fitted-normal and fitted-uniform resampling
laws, actual refitted maxima, finite-sample laws, conditional moment/CDF limits
and simulation variance statements. Zero fitted variance is a point mass;
interior normal likelihood maximization is only claimed with positive empirical
variance. Uniform endpoint normalization uses the fitted endpoint conditionally
and the true endpoint for the original sampling pivot.

The seven Poisson modules were reviewed in full against their model and source:
normalized product masses, all-zero likelihood boundary, open-domain suprema,
actual derivatives and information, two verified L’Hôpital steps, same-sample
Slutsky equivalence, and exact/asymptotic calibration. The Bernoulli odds and
likelihood-ratio modules were independently reviewed, including their different
finite-boundary conventions. Gamma–Poisson concentration uses actual conjugate
posterior moments and IID sampling consistency. Rectangle inversion retains
absolute errors and positive scales.

The exact quadratic bootstrap-bias formulas and central fourth-moment sum
expansion were reviewed independently. Taylor expectation bounds explicitly
establish integrability. Monte Carlo error is measured on the actual product
of complete resamples, then transferred to the actual joint data/index law.
Finite-variance Lipschitz simulation control uses n/B→0 for the 1/n bias scale.
This statement is distinct from both first-order interval coverage and a claim
about the expectation of the corrected estimator.

The classifier guarantee uses the actual bounded-observation Hoeffding bound,
a finite union bound and a rational exponential-series calculation; no
independence between classifiers is assumed. The probability examples preserve
the strict thirty-percent threshold and both endpoints of the income band.

The additional semantic review checked actual expected bootstrap-corrected
bias separately from bias-estimation consistency. The former uses bounded IID
observations, C³ regularity, bounded second and third derivatives, and explicit
domination; the simulation theorem instead proves convergence in probability
under joint data/index laws. Bernstein's exact constants, the zero-variance
case, and its conditional comparison with Hoeffding were checked. The uniform
endpoint counterexample uses the actual full-sample information N²/θ², so it
does not incorrectly invoke the regular information-additivity identity.

Independent review also passed the ordinary finite-second-moment mean
intervals, grid confidence sets (including zero coverage off the grid), the
squared-mean delta limit, and both known-variance normal information identities.
The Edgeworth cancellation theorem concerns a fixed argument and explicitly
assumes the actual CDF expansions; it does not establish their existence.
The Erlang CDF proof integrates the actual Gamma density and checks rational
numerical bounds. Its Gaussian-square interpretation is a separate next step.

The complete 284-module snapshot passed the source scan, 8991-job build and
transitive proof audit: 3760 declarations, including 3358 theorem declarations,
with no prohibited dependencies. Verification-copy parity covered 291 files:
256 unchanged Git object hashes and 35 changed/new byte comparisons. The
34 added modules contain 230 source theorem declarations, 34 definitions and
4 instances. This certifies the included statements with their recorded
hypotheses; the remaining scope qualifications still apply.

## Final source-application review (2026-10-02)

`ConditionalPrediction` removes the finite-risk restriction from L1 Theorem 6.
The competitor is any real-valued predictor measurable with respect to the
conditioning information. If its squared loss is finite, square integrability
follows from that of Y and its residual; otherwise the extended-risk comparison
is immediate. Independent semantic review passed this argument.

`DegenerateInfluence` constructs the actual equal-mass ±1 law, with mean zero,
variance one and finite moments of all orders. For h(mean,variance)=variance
the derivative is nonzero, but the squared-centered influence is identically
zero. Thus the extra positive influence-variance assumption used for normal
calibration is necessary even with positive population variance. This
counterexample passed independent semantic review.

`ChiSquaredGamma` identifies the actual even-dimensional Gaussian-square law
with Gamma(shape=dimension/2, rate=1/2), using polar integration and the
squared-radius Jacobian. The existing exact Erlang CDF yields the certified
χ²₁₀₀ CDF bound 0.246<F(90)<0.247, its comparison with the 5% critical value,
and the source sample-variance test's nonrejection. Independent review checked
the full bridge and the numerical decision.

`SymmetricHighestDensity` derives quantile reflection and equal-tail content
for any measurable integrable normalized nonnegative density which decreases
with distance from a center. Compact support and nonstrict monotonicity are
allowed. The equal-tailed interval is between the strict and weak density
superlevel sets and has minimum Lebesgue volume. Density plateaus may give
other minimizers; uniqueness is not claimed. Independent review passed.

`BernoulliScoreTests` derives the actual count/product likelihood score, its
information-based LM formula, the two-sided quadratic confidence inequality,
the IID χ²₁ limit, asymptotic null size and pointwise coverage.
`BernoulliWilks` derives the LR limit by an exact success/failure deviance
decomposition and proved removable quadratic coefficients, then connects it
to the actual open-parameter product likelihood supremum. All-zero and
all-one observed samples are retained. Root and independent agent review
passed the formulas, parameter domains, scales, and actual-model limits.

`NormalSampleConjugacy` connects the actual product of all normalized Gaussian
observation densities and the normal prior measure to the exact posterior,
its mean/variance and posterior-loss minimizer. The empty sample is included
separately. With positive fixed noise/prior variances, actual IID sampling
implies almost-sure posterior concentration via the sample-mean strong law
and posterior second moments.

`NormalHierarchicalGaussian` starts with independent prior and error draws,
derives the conditional IID observation law, and identifies the full joint
Gaussian vector. Its observation block has covariance w·11ᵀ+vI, the
observation/latent cross-covariances are w, and latent variance is w. Setting
v=1 gives the printed source matrix. Zero variances and the empty sample
remain valid in this joint-law theorem. Both modules passed two independent
semantic reviews.

`BernoulliSampleInformation` derives actual full-sample moments and information
n/[p(1−p)]. `BernoulliCramerRao` differentiates the finite weighted expectation
of an arbitrary estimator and derives the score identity needed by Cramér–Rao.
It then proves the source sample-mean attainment and uniform minimum-variance
unbiasedness, including both degenerate endpoints. The competing estimator
is unbiased across the model, not merely at the parameter being evaluated.

`PivotalStatistics` gives the explicit common-law definition and generic
confidence-region inversion. Arbitrary measurable acceptance regions transfer
exact probabilities, including discrete laws; quantile intervals additionally
require an atomless probability law. Independent review passed these scopes.

`NormalPowerMonotonicity` retains both rejection tails. Its strict power
comparison requires a positive cutoff and increasing absolute effect;
sample-size strictness additionally requires nonzero effect and positive
standard deviation. Large-effect convergence allows changing signs. The
actual IID normal sampling experiment supplies the power limit as sample
size grows. Root review checked these qualifications and the actual Gaussian
density/CDF connection.

The final definition review added `ConfidenceLevel`: the actual real infimum
of coverage, its equivalence with the existing lower-bound predicate, bounds
in [0,1], and exact level for constant coverage. Nonempty parameter spaces
are explicit where needed; attainment of the infimum is not assumed. This
closes the numerical part of L11 Definition 2. Independent review passed.

The 296-module checkpoint passed the complete source scan, 9003-job build
and transitive dependency audit: 3945 declarations, including 3530 theorem
declarations. All 303 proof/audit/dependency files matched the verification
copy: 290 unchanged Git object hashes and 13 changed/new byte comparisons.
Its 12 added modules contain 88 source theorems, 13 definitions and 2 instances.
The subsequent confidence-level and final Monte Carlo applications are audited
in the final verification summary below.

`MonteCarloStudentizedIntervals` applies actual joint conditional-quantile
convergence to bootstrap-t intervals, with each resample's own standard error.
The main theorem derives both the sampling and conditional limits from IID
finite fourth moments and positive variance; any B(n)→∞ suffices. Rare
nonpositive observed scales are controlled separately from zero resample
scales. The denominator-N versus denominator-(N−1) variance conversion is
an exact endpoint identity for N>1: positive scaling of each simulated error
rescales its empirical quantile and cancels against the observed standard
error. Zero variances are included. The source-convention theorem discards
only the first N=1 index in taking the limit. Root and independent agent
semantic reviews passed both the generic argument and the source application.

`MonteCarloBiasExpectation` proves that every positive finite number of
resampling replicates has the correct conditional expectation. It transports
that identity to the actual uniform-index experiment, derives joint
integrability from bounded observations and a continuous transform, and uses
Fubini to identify the simulated correction's expected bias with that of the
exact correction. The final o(1/n) bias result uses the established bounded-IID,
C³ and bounded-second/third-derivative hypotheses. It needs neither Lipschitz
continuity nor a growth condition on B. This does not weaken the separate
replication conditions for bias-estimation precision or confidence coverage.
Independent review checked the complete argument and quantifiers.

## Final verification and source accounting (2026-10-02)

The final combined project passed `scripts/check.sh`: **299 imported source
modules**, a successful **9006-job build**, and **3978 audited declarations**,
including **3559 theorem declarations** when private/compiler-generated
declarations are counted. There were no forbidden source tokens or prohibited
transitive logical dependencies. All **306** proof/audit/dependency files
matched the verification copy: 290 unchanged Git object hashes and 16
changed/new byte comparisons. Relative to the preceding pushed checkpoint,
the 15 added modules contain 107 source theorem declarations, 16 definitions
and 2 instances. The thirteen original PDFs remain unchanged.

The source index was checked against the extracted numbered inventories:
all **41 theorems**, **24 definitions** and **54 examples** are mapped exactly
once, and both numbered lemmas are recorded. All 170 module links in the
source index resolve. Independent mathematical review covered the new source
applications, hypotheses, finite-sample conventions and limit quantifiers.
The final review found no additional well-specified concrete example awaiting
a proof. The source's incorrect assertions use corrected statements or
checked counterexamples; unspecified general regularity, complete-class and
MCMC remarks retain explicit scope qualifications. This does not assert
unconditional versions of those remarks or a line-by-line copy of each
informal proof.

## Independent source and formulation review (2026-10-04)

Starting revision: `232827534756df5da34649d2946eee4aedbd7167`. This fresh review
used the supplied thirteen PDFs, newly extracted text and rendered checks of
L3 p9, L5 p13 and L11 p5. All thirteen PDFs were compared with the supplied
export and matched. Three independent topic reviews were combined with a
separate review of the probability and asymptotic foundations. The review
compared definitions, final statements and critical proof arguments; it does
not claim that every line of all previously compiled proofs was reread.

### Findings and corrections

1. **L5 Remark 1 was missing.** `PropensityScoreBalancing` now defines the
   actual propensity score as the conditional expectation of the binary
   treatment indicator given the covariates. Tower and pullout identities
   prove conditional independence of treatment and covariates given that
   score. Conversely, every measurable balancing coarsening of the covariates
   measurably recovers the score almost surely. The conditional-independence
   results use a standard Borel sample space. There is no overlap hypothesis;
   overlap is needed separately for the ATE formula. The new module received
   two independent semantic reviews in addition to the integration review.
2. **L11 Remark 1's exact limits needed separate definitions.** The existing
   pointwise and uniform coverage predicates correctly express lower bounds,
   but do not express the displayed exact limits. `AsymptoticCoverage` adds
   exact pointwise coverage and an exact limiting infimum of coverage. It
   proves their lower-bound implications and, under exact pointwise coverage
   on a nonempty parameter space, equivalence of the exact infimum limit with
   uniform lower coverage. An infimum limit alone need not force exact
   pointwise coverage. This distinction is witnessed by a fair-coin experiment
   with coverage one half at one parameter and one at another. A second
   fair-coin experiment has parameter space ℕ and region
   `{θ | θ < n ∧ x = true}`: each fixed parameter eventually has coverage one
   half, but parameter n has coverage zero at sample size n. This proves the
   source's moving-undercoverage warning using actual probability measures.
   Independent cross-review checked both examples and the general implications.
3. **Source-index corrections.** L5 Examples 6, 7 and 8 are now separated into
   weighted-estimator calculations, mean/variance consistency and the CLTs.
   The unknown-variance normal mean insufficiency passage is in Example 10,
   not Example 11. All fifteen numbered remarks now have individual rows;
   the semiparametric-efficiency citation and deferred general bootstrap
   discussion retain explicit scope qualifications.
4. **Two documentation corrections.** The L3 p9 big-O definitions do have
   absolute-value bars in the PDF; extraction had obscured them. The Lean
   definitions already had the correct absolute-value formulation. Bootstrap
   replication-growth requirements apply to simulation precision and coverage,
   while the proved expected-bias correction permits any positive finite
   replication count. The coverage ledger now makes this distinction explicit.

### Checks on the existing formulations

| Area | Main checks |
| --- | --- |
| Probability, sampling and convergence | Event-based CDFs, measurable variables, actual sampling laws, n versus n−1 denominators, independence of normal projections, Gaussian covariance and conditioning, moment/integrability conditions, delta-method scales, Cramér–Wold directions, triangular-array limits, stochastic-order quantifiers and the actual empirical-CDF supremum. |
| Sufficiency and estimation | One parameter-independent conditional kernel or estimator, almost-sure measurable recovery, actual density factorizations and support, common versus parameter-specific null sets, and explicit nonvacuous regularity for information identities and Cramér–Rao. |
| MLE and testing | Actual likelihoods and degenerate boundary cases, derivative and moment assumptions, consistency and interiority, dimensions and inverse/sandwich covariance, score/Wald/LR normalization, full-sample randomized-test competitors, and exact versus asymptotic calibration. |
| Confidence sets | Event inversion, atomless versus discrete quantiles, nonempty parameter spaces where needed for infima, shared-baseline covariance, positive scales, off-grid coverage failure, and pointwise versus uniform limit quantifiers. |
| Bootstrap and simulation | Actual empirical product/index laws, finite second versus fourth moments, positive influence variance, ties in empirical quantiles, zero observed versus resampled variances, joint data/seed probabilities, and expected correction versus simulation precision. |
| Bayesian and decision theory | Posterior normalization, affine Jacobians, rate/scale conventions, genuine local-quadratic/envelope premises, exact HPD plateau splitting and infinite-volume competitors, nonnegative extended risks, all measurable competing decisions, and noncircular singular-risk integrability. |
| Causal, survey and weighted estimation | Treatment/covariate conditioning, separate identification assumptions, marginal versus joint inclusion probabilities, design normalization, and rank/nonzero-denominator conditions. |

No additional mathematical defect was found in the inspected statements and
proof arguments. This is a review finding, not a machine-certified equivalence
between prose and Lean. Explicit limitations remain: curved asymptotic results
use supplied local charts and identity-information coordinates; logistic
information is conditional on fixed covariates; generic rectangle coverage
needs a calibrated maximum-statistic cutoff. Unspecified universal regularity,
semiparametric efficiency, complete-class and MCMC theories, and existence of
the source's undeveloped Edgeworth expansions are not claimed as unconditional
theorems. Earlier dated counts above describe historical checkpoints.

The fresh numbered inventory contains **41 theorems, 24 definitions, 54
examples, 15 remarks and 2 lemmas**. Expanding every grouped range in the
source index and coverage ledgers gives the same IDs, with no omissions,
extras or duplicates. All **200** relative links in the source index resolve,
including 198 module links to 156 distinct Lean files. The thirteen committed
PDFs match the supplied export. The verification copy matches all **308**
proof/audit/dependency files: 304 unchanged Git object hashes and four
changed/new byte comparisons.

The final combined `scripts/check.sh` run passed: **301 imported source
modules**, a successful **9008-job build**, and **4012 audited declarations**,
including **3586 theorem declarations** when private/compiler-generated
declarations are counted. No forbidden source tokens or prohibited transitive
axiom dependencies were found. The two added modules contain 18 source theorem
declarations (including four private helpers), seven definitions and two
instances. The only edit to an existing Lean module clarifies two docstrings;
its definitions and theorem statements are unchanged.

## Second independent review (2026-10-04)

Starting revision: `4f6ed7f8a6a765cc2c3d680e735bcc5aadb6a0d7`. The reviewers
rotated topics for this pass and read the source passages directly. The review
covered 120 distinct Lean modules, including the new corollaries below, plus
the convergence definitions used by several of them. It inspected statements,
definitions and proof arguments; it does not claim a fresh reading of every
line in the entire project or an independent reconstruction of Mathlib.
Rendered checks included L1 pp3–4 and p14, L3 p9, L4 p2 and L13 p3.

### Findings

No incorrect existing Lean statement or proof was identified in the inspected
material. Two improvements make the source correspondence more explicit:

- `ProbabilityIdentities` exports six corollaries for L1 pp3–4. Conditional
  probability agrees with the actual normalized restriction measure; a nonnull
  conditioning event gives a probability measure and the conditional-complement
  formula. The two-event total-probability formula yields the exact printed
  Bayes denominator. The CDF increment is the probability of `(a,b]`, allowing
  atoms and coincident endpoints. These follow from existing general results
  and Mathlib's measure API; no existing definition or theorem was weakened.
  A separate reviewer checked all six proofs against the rendered source.
- The L11 coverage-ledger sentence now says that **uniform lower coverage
  implies pointwise lower coverage**. Its previous abbreviated wording could
  be confused with the newly exported exact-limit notions. The previously
  proved counterexample shows why that distinction is necessary.

### Fresh mathematical checks

| Area | What was checked |
| --- | --- |
| Empirical processes | All nine DKW modules, the actual measurable supremum over the whole real line, one common almost-sure event, atomic-law quantile coupling, open/closed tail conventions, and a deterministic common exponential tilt chosen before the sample. The proof uses a two-sided union bound only, without a union bound over grid points. |
| Triangular arrays and stochastic order | Actual within-row independence, second moments and Lindeberg truncation for every positive threshold; derived negligibility; Lyapunov's arbitrary positive exponent increment; varying row spaces; separate diverging two-sample sizes; uniform-in-n stochastic boundedness; zero-variance and zero-scale qualifications. |
| MLE and inference | Derivative-based likelihood expansions, consistency and interiority, rare singular finite-sample curvature, inverse/sandwich covariance orientation, dependent full/restricted scores, chart/rank hypotheses, total-size two-sample scaling, shared-baseline contrast covariance, and posterior content versus frequentist coverage. |
| Conditional and Gaussian laws | Actual regular conditional measures under the marginal law, exceptional zero/infinite density fibers, absolute inverse Jacobians, positive definite conditioning blocks, potentially singular residual covariances, and the printed hierarchical-normal covariance matrix. |
| Posterior and decision results | Positive evidence and properness; actual normalized sample likelihoods; rate/scale conventions; uniform bounds over all measurable events; affine determinants and covariance orientation; extended nonnegative risk; predictive-almost-everywhere minimization; exact HPD plateau splitting; quantile-reparameterization restrictions. |
| Finite-sample examples | First-success and trimmed/median conventions, Bernoulli/binomial/Poisson laws and boundary parameters, binomial generating-function counts including zero totals, the actual uniform-square law, finite-space unbiasedness obstruction, finite-population and survey normalization, positive joint inclusion probabilities, observed-outcome randomization, oracle-weight dependence on unknown parameters, and exact quadratic bootstrap bias. |

The mathematical scope restrictions remain part of the results. In particular,
the general constrained/curved inference theorems use supplied charts and
explicit regularity; the nondegenerate two-sample theorem requires both
population variances positive; uniform CDF convergence requires an atomless
limit; decreasing quantile transformations retain their support/continuity
conditions. The stronger sufficient conditions in these theorems are recorded
in the coverage ledgers and are not claims of unconditional source results.

The fresh source inventory still has **41 theorems, 24 definitions, 54
examples, 15 remarks and 2 lemmas**. All 136 numbered IDs match the expanded
index/ledger rows exactly, without omissions or duplicates. All **201**
source-index links resolve. The verification copy matches all **309**
proof/audit/dependency files: 307 unchanged Git object hashes and two
changed/new byte comparisons. Inspection of all source options and declaration
commands found no kernel-check bypass or custom declaration-insertion command.

The final combined `scripts/check.sh` run passed: **302 imported source
modules**, **9009 build jobs**, and **4021 audited declarations**, including
**3595 theorem declarations** when private/compiler-generated declarations are
counted. The new module contains six source theorem declarations and introduces
no new definitions. Both the forbidden-token scan and the transitive axiom
audit passed. Existing Lean definitions and theorem statements are unchanged.

## Third independent review (2026-10-04)

Starting revision: `2ef8d6c14cee6623ac990b486f0d4860827f98ca`. Reviewers rotated
topics again, comparing the source passages with the definitions, quantifiers,
hypotheses, conclusions and proof arguments in **158 distinct Lean modules**.
This comprised 138 full-file reads and 20 additional files reviewed through
all declarations and selected core proofs. No new mathematical defect or
incorrect source transcription was found in the inspected material. This pass
changes only this audit record; no Lean statement or proof was changed.

### Mathematical checks

| Area | What was checked |
| --- | --- |
| Sufficiency and optimal estimation | One parameter-independent conditional kernel and Rao–Blackwell estimator; parameter-specific exceptional null sets; both directions of sigma-finite Fisher–Neyman factorization; measurable almost-sure minimality and likelihood recovery; varying-support endpoint decoders; actual normal, regression, Cauchy, Gumbel and binomial experiments. The binomial conditional estimator retains counting coefficients, the zero-total branch, feasible totals and boundary parameters. Bernoulli UMVU quantifies over every model-unbiased competitor. |
| Information and causal identification | Actual derivatives of normalized densities, integrable derivative bounds, differentiation of the estimator's expectation, and unbiasedness throughout an open parameter domain. The explicit Bernoulli model satisfies the regularity premises. The uniform-endpoint example proves nonzero expected score and failure of information additivity. Treatment identification uses conditional independence, consistency and overlap; the propensity-score balancing result does not need overlap. IV identification retains instrument relevance and the binary-group formula requires nonempty groups. |
| Exact sampling and confidence sets | Actual chi-square, Student and F constructions; n versus n−1; correct residual degrees of freedom; almost-sure positive random denominators; known versus nuisance variance; reversed quantile endpoints in variance inversion. Pratt's identity permits infinite expected length, and its optimality theorem requires the stated UMP tests. No unrestricted shortest-length claim is made for ordinary two-sided Student intervals. |
| Likelihood ratios and testing | Actual likelihood suprema, positivity and attainment conditions; empty and constant samples; Bernoulli and Poisson open-domain suprema at boundary data. Neyman–Pearson handles null-density zeros and the zero-threshold necessity case; MLR retains changing supports and randomized ties. Normal UMP/UMPU results compare all measurable randomized full-sample tests with known positive variance. Exact Gaussian calibration remains separate from Bernoulli, Poisson, ordinary t and Welch asymptotic calibration. |
| Bootstrap and simulation | Actual empirical product/index laws with observation multiplicities; changing conditional-law CLTs; common almost-sure sets; derived variance and smooth-statistic remainders; n−1 corrections and rare zero scales. Simulated first-order interval coverage requires replication counts tending to infinity; expected bias correction permits any positive finite count under the stated integrability conditions. Edgeworth expansions remain explicit assumptions at a fixed evaluation point. The empirical-bootstrap maximum counterexample is distinct from the valid fitted-uniform parametric pivot. Off-grid confidence coverage is zero, as the source correction records. |
| Concentration and convergence | Hoeffding/Bernstein constants, centered observations, independent summands, zero variance, and the explicit range in which Bernstein improves the Hoeffding bound. Classifiers may share a test set; the union bound does not assume independence between classifiers. The 26,492-observation guarantee uses a proved rational exponential bound. Convergence definitions, the uncorrelated weak law and alternating-uniform counterexample have the intended quantifiers. |
| Quantiles and further examples | Lower generalized inverses, open/closed tail bracketing, ties, ceiling ranks, atomless exact calibration and data-dependent critical values. Logistic score roots give global maxima; full rank gives uniqueness without asserting existence, and complete separation precludes finite maxima. Wald ellipse projection uses the joint cutoff. A nonzero derivative alone does not imply positive influence variance. Gamma–Poisson concentration concerns the actual posterior and uses the rate/scale conversion. |

The review preserves the documented scope restrictions. In particular, L5
pp15–16's rejection-based Monte Carlo evaluation of a Rao–Blackwell estimator
is an implementation suggestion. The exact conditional law, estimator,
unbiasedness and variance reduction are proved; an accepted-draw stopping-time
sampler and its repeated-simulation convergence are not separately formalized
or claimed in the source index. General model-specific regularity, unrestricted
pointwise minimality and the other previously documented qualifications remain
unchanged. This review is not a fresh reading of every project dependency or a
machine-certified equivalence between the PDFs and the Lean statements.

### Verification

The fresh combined `scripts/check.sh` run passed: **302 imported source
modules**, a successful **9009-job build**, and **4021 audited declarations**,
including **3595 theorem declarations** when private/compiler-generated
declarations are counted. The source scan found no forbidden tokens, and the
transitive dependency audit permitted only `propext`, `Classical.choice` and
`Quot.sound`. Inspection of source options and declaration commands found no
custom declaration insertion or kernel-check bypass.

All **309** proof/audit/dependency files in the verification copy match their
unchanged Git object hashes. All thirteen committed PDFs match the supplied
export byte for byte. The independently reconstructed inventory again matches
all **136** numbered source IDs exactly: 41 theorems, 24 definitions, 54
examples, 15 remarks and 2 lemmas, with no omissions or duplicates. All **201**
source-index links resolve. Rendered source checks included L3 p4's Bernstein
constants and classifier budget and L6 p7's Cramér–Rao formulation.
