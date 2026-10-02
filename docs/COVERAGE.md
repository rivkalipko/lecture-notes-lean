# Coverage ledger

This ledger covers all **32 numbered theorems** in Lectures 1–6, followed by
definitions and other material. A qualified row does not count as an
unconditional proof of the general source statement.
Statements marked **proved** include the explicit measurability, integrability,
nonzero-denominator, and regularity hypotheses described below and in
[SOURCE_AUDIT.md](SOURCE_AUDIT.md).

The new Lectures 7–13 contain **9 additional numbered theorems** (41 total).
Their complete numbered-theorem inventory and other material are tracked in
[NEW_NOTES_COVERAGE.md](NEW_NOTES_COVERAGE.md), with corrections in
[NEW_NOTES_AUDIT.md](NEW_NOTES_AUDIT.md). This original ledger remains the
Lectures 1–6 inventory.

Declaration names are in the `LectureNotes` namespace except where a nested
namespace is shown. The files linked below are all imported by `LectureNotes.lean`.

The [source index](SOURCE_INDEX.md) separately maps all 24 numbered definitions,
54 numbered examples and both numbered lemmas across the thirteen lectures.

## Numbered theorems

| Source | Status | Formal declarations and qualifications |
| --- | --- | --- |
| L1 T1, probability laws | Proved | [Foundations](../LectureNotes/Foundations.lean): `prob_empty`, `prob_univ`, `prob_compl`, `prob_mono`, `prob_bounds`, `inclusion_exclusion`, `union_bound`. Derived from Mathlib measures. |
| L1 T2, continuity of probability | Proved | [ProbabilityLaws](../LectureNotes/ProbabilityLaws.lean): `probability_continuous_from_below`, `probability_continuous_from_above`. |
| L1 T3, conditional probability | Proved for finite partitions | `multiplication_rule`, `total_probability` in ProbabilityLaws; `conditional_probability`, `bayes` in Foundations. Conditioning denominators are nonzero. |
| L1 T4, expectation and variance | Proved | Foundations: `expectation_const`, `expectation_linear`, `variance_eq_second_moment_sub_mean_sq`, `variance_scale`, `variance_translate`. Integrable or square-integrable variables as appropriate. |
| L1 T5, iterated expectations | Proved | [ConditionalExpectation](../LectureNotes/ConditionalExpectation.lean): `iterated_expectations`, using Mathlib's conditional expectation on a sub-sigma-algebra. |
| L1 T6, best predictor | Proved for every measurable competing predictor | [ConditionalPrediction](../LectureNotes/ConditionalPrediction.lean): `conditional_expectation_best_predictor_extended` uses extended nonnegative risks, permitting infinite-loss competitors. Finite competing loss implies square integrability and reduces to the proved orthogonal decomposition in ConditionalExpectation. |
| L2 T1, normal sampling | Proved | [NormalSampling](../LectureNotes/NormalSampling.lean): `normal_sampleMean`, `normal_sampleMean_independent_sampleVariance`. [NormalSamplingDistribution](../LectureNotes/NormalSamplingDistribution.lean): `normal_sampleVariance`, `normal_studentized_mean`. All statements involving sample variance require `n > 1`; the chi-square and t laws also require positive population variance. `residualSpace_projection` and `residualSpace_finrank` prove the centering projection and its dimension `n - 1`. |
| L2 T2, finite population | Proved | [FinitePopulation](../LectureNotes/FinitePopulation.lean): `simpleRandomSampling_mean`, `simpleRandomSampling_variance`. The probability model is uniform on all n-element subsets; marginal/pair inclusion probabilities are proved by counting. Assumes `0 < n ≤ N` and `1 < N` for the variance formula. |
| L2 T3, Horvitz–Thompson | Proved | [SamplingMoments](../LectureNotes/SamplingMoments.lean): `horvitzThompson_unbiased`, `horvitzThompson_variance` prove the moment calculation with nonzero denominators. FinitePopulation: `horvitzThompson_design_unbiased`, `horvitzThompson_design_variance` give the actual subset-design statements with positive marginal inclusion probabilities and a nonempty population. |
| L3 T1, Jensen | Proved | [Inequalities](../LectureNotes/Inequalities.lean): `jensen_inequality`, from Mathlib Jensen, with integrability of both the variable and convex transform. |
| L3 T2, Markov | Proved | `markov_inequality`, nonnegative integrable random variable and positive threshold. |
| L3 T3, Chebyshev | Proved | `chebyshev_deviation`, with the actual absolute-deviation event; `chebyshev_inequality` also gives the squared-deviation form. |
| L3 T4, Hölder | Proved | `holder_absolute`, for arbitrary signs using absolute values; `holder_inequality` gives the nonnegative form. |
| L3 T5, Hoeffding | Proved | [Concentration](../LectureNotes/Concentration.lean): `hoeffding_lemma`, `hoeffding_sum`, `hoeffding_sampleMean`. Independent observations suffice. The displayed sample-mean bound has exponent `-2*n*epsilon^2/(b-a)^2`, with `a < b`. |
| L3 T6, Cramér–Wold | Proved | [CramerWold](../LectureNotes/CramerWold.lean): `cramer_wold`, in finite-dimensional real inner-product spaces. Reverse direction uses characteristic functions and Lévy's theorem. |
| L3 T7, convergence implications | Proved | [Convergence](../LectureNotes/Convergence.lean): all five implications are separate theorems. Mean and mean-square convergence include integrability hypotheses. |
| L3 T8, Slutsky | Proved | `slutsky_add`, `slutsky_mul`, `slutsky_div`; division requires a nonzero limiting constant. DeltaMethod: `slutsky_mul_zero` gives the source's additional convergence-in-probability conclusion when the multiplier tends to zero. |
| L3 T9, continuous mapping | Proved | `continuous_mapping_almost_sure`, `continuous_mapping_probability`, `continuous_mapping_distribution`; mapping at a constant limit also has a theorem requiring continuity only there. |
| L3 T10, Chebyshev WLLN | Proved | [WeakLaw](../LectureNotes/WeakLaw.lean): `weak_law_uncorrelated`. Derives the variance of the centered sample mean and convergence from the source's `n^-2 sum variance -> 0` condition. |
| L3 T11, SLLN | Proved via Mathlib | [LargeSample](../LectureNotes/LargeSample.lean): `strong_law_of_large_numbers`; pairwise independence and identical laws suffice. |
| L3 T12, CLT | Proved via Mathlib and Cramér–Wold | LargeSample: `central_limit_theorem`; [MultivariateCLT](../LectureNotes/MultivariateCLT.lean): `multivariate_central_limit_theorem`. The multivariate target is specified by its Gaussian projection laws with matching variances. [VectorScoreCLT](../LectureNotes/VectorScoreCLT.lean) constructs the canonical multivariate Gaussian target from the actual coordinate covariance matrix, proves that matrix is positive semidefinite, and proves the CLT with that target, allowing singular covariance. Linear transformations have the proved covariance `A S Aᵀ`. |
| L3 T13, Lindeberg–Feller | Proved | [LindebergFeller](../LectureNotes/LindebergFeller.lean) proves the triangular-array theorem from independence, centering, second-moment normalization, and the actual Lindeberg truncated-moment condition. `lindeberg_feller_sequence` gives the source's non-identically distributed sequence and normalization by the square root of the sum of variances, positive eventually. Characteristic-function errors and asymptotic negligibility are derived; no CLT conclusion or third moment is assumed. [Lyapunov](../LectureNotes/Lyapunov.lean) proves the higher-moment sufficient condition for every positive real exponent increment. |
| L3 T14, delta method | Proved | [DeltaMethod](../LectureNotes/DeltaMethod.lean): `delta_method`, `delta_method_normal`. Uses the measurable divided difference, the exact `sqrt n` rate, and proves the transformed Gaussian variance. Global continuity and differentiability at the limit suffice; a zero derivative is allowed and gives a degenerate limit. |
| L4 T1, empirical CDF | Proved | [EmpiricalDistribution](../LectureNotes/EmpiricalDistribution.lean): `empiricalCDF_unbiased`, `empiricalCDF_variance`, `empiricalCDF_consistency`, `empiricalCDF_strong_consistency`. These are pointwise statements for each fixed threshold. |
| L4 T2, Glivenko–Cantelli / DKW | **Proved** | [EmpiricalUniform](../LectureNotes/EmpiricalUniform.lean) proves almost-sure uniform convergence on the entire real line, almost-sure convergence of the actual supremum error, and convergence in probability. Arbitrary real IID laws, including discrete and mixed laws, are allowed. Open and closed lower tails at finite quantile partitions handle atoms. [EmpiricalSupMeasurable](../LectureNotes/EmpiricalSupMeasurable.lean) proves that the supremum error equals a countable rational supremum and is measurable. [DKW](../LectureNotes/DKW.lean) proves the sharp two-sided bound for the actual supremum error: `P(sup \|F_n−F\| > ε) ≤ 2 exp(−2nε²)` for every positive sample size and ε>0. Generalized-inverse coupling allows arbitrary IID real laws, including atoms. A reversed-threshold martingale and a proved common exponential tilt control all grid crossings simultaneously; the argument does not pay a union bound over grid points. |
| L5 T1, MSE decomposition | Proved | Foundations: `mse_eq_variance_add_bias_sq`; Estimation: `mse_bias_variance_decomposition`. Squared-error expectation is a genuine integral, not an assumed calculation. |
| L5 T2, factorization | Proved for sigma-finitely dominated standard Borel experiments | [FisherNeymanGeneral](../LectureNotes/FisherNeymanGeneral.lean): `fisherNeyman_general` proves equivalence between a common conditional-law kernel and measurable density factorization relative to the original dominating measure. Carriers may have infinite total mass and supports may vary with the parameter. [DominatingMixture](../LectureNotes/DominatingMixture.lean) proves the countable dominating-mixture construction; disintegration gives the conditional law without integrating over null fibers. The finite positive-support theorem is retained in [Sufficiency](../LectureNotes/Sufficiency.lean). |
| L5 T3, exponential family statistic | Proved for dominated real-observation families | [ExponentialFamilySufficiency](../LectureNotes/ExponentialFamilySufficiency.lean) proves that the actual IID product density factors through the vector of canonical sums, then proves sufficiency of those sums. A common measurable carrier may vanish or have infinite integral; the given single-observation densities must define probability measures. Empty samples are allowed. |
| L5 T4, minimal sufficiency | **Partial generalization** | [MinimalSufficiency](../LectureNotes/MinimalSufficiency.lean) defines minimality using one measurable reconstruction from every sufficient standard Borel statistic, under every model law. Finite or countable likelihood-ratio recovery proves this property, including a dominating mixture in [MixtureMinimalSufficiency](../LectureNotes/MixtureMinimalSufficiency.lean). [NormalSufficiency](../LectureNotes/NormalSufficiency.lean) verifies recovery and minimality for the full normal sample with known positive variance. [UniformEndpointMinimal](../LectureNotes/UniformEndpointMinimal.lean) proves minimality of the maximum for the entire positive uniform-endpoint experiment, recovering it from countably many rational support cuts. [UniformLocationMinimal](../LectureNotes/UniformLocationMinimal.lean) proves minimum/maximum minimality for translated unit intervals, and [TriangularEndpointMinimal](../LectureNotes/TriangularEndpointMinimal.lean) proves maximum minimality for the actual density `2x/θ²` on `(0,θ)`. [LikelihoodRepresentationMinimal](../LectureNotes/LikelihoodRepresentationMinimal.lean) derives measurable recovery from an injective countable likelihood-ratio representation on a standard Borel statistic space. The pointwise ratio criterion is proved in both directions for finite strictly positive models in Sufficiency. The literal unrestricted pointwise conclusion is disproved by [PointwiseMinimalityCounterexample](../LectureNotes/PointwiseMinimalityCounterexample.lean), using different everywhere-positive density versions of one Gaussian law. The valid almost-sure criterion still requires measurable reconstruction conditions, as stated in the general results. |
| L5 T5, Rao–Blackwell | Proved on standard Borel sample spaces | [RaoBlackwell](../LectureNotes/RaoBlackwell.lean): `rao_blackwell_sufficient` constructs one measurable function of the sufficient statistic, valid for every parameter, and proves square integrability, mean preservation, and MSE reduction. `rao_blackwell_unbiased_sufficient` proves unbiasedness and variance reduction. `IsSufficientStatistic` means that one Markov kernel gives the conditional distribution of the data under every model measure. Estimators are measurable and square integrable under each measure. |
| L6 T1, information equalities | Proved under explicit corrected regularity | [RegularDensity](../LectureNotes/RegularDensity.lean): `RegularDensity.first_information_equality`, `second_information_equality`, `score_is_log_derivative`, `logHessian_is_score_derivative`. Normalization is differentiated twice using integrable bounds on density derivatives. [RegularCramerRao](../LectureNotes/RegularCramerRao.lean) connects weighted integrals to the actual probability model. |
| L6 T2, Cramér–Rao | Proved under explicit corrected regularity | RegularCramerRao: `RegularDensity.cramer_rao` proves the bound from a density model, including differentiation of the estimator's expectation; `RegularDensity.cramer_rao_unbiased` assumes unbiasedness throughout the open parameter domain. [Information](../LectureNotes/Information.lean): `cramer_rao_bound`, `cramer_rao_unbiased_from_score_identity`, `fisherInformation_sum` isolate the covariance argument and information additivity. |

## Definitions and other material

| Material | Core coverage | Further coverage and limitations |
| --- | --- | --- |
| L1 probability foundations | Mathlib `MeasurableSpace`, `Measure`, `IsProbabilityMeasure`; measurable `Event` and `RandomVariable`; conditional, pairwise, joint, and conditional independence of events; `cdfOf` with probability interpretation, monotonicity, limits, and right continuity | ProbabilityExamples formalizes both opening sample-space/event examples and the stated sigma-algebra closure consequences. |
| L1 moments and covariance | Integral expectation, variance, covariance identities, independence implies zero covariance, zero variance implies constancy almost everywhere, covariance Cauchy–Schwarz bound; [ChiSquaredMoments](../LectureNotes/ChiSquaredMoments.lean) proves the fourth standard-normal moment and chi-square mean/variance with square integrability | [Correlation](../LectureNotes/Correlation.lean) defines correlation and proves its bound and perfect-correlation characterization by almost-sure affine dependence under positive variances. [BernoulliBinomialMoments](../LectureNotes/BernoulliBinomialMoments.lean) and [PoissonMoments](../LectureNotes/PoissonMoments.lean) prove the actual MGFs, means, second moments and variances, including boundary parameters. General joint and marginal formulas are now proved in JointDistributions, as detailed below. |
| L1 distribution theory | Normal laws through Mathlib; [GaussianQuadraticForms](../LectureNotes/GaussianQuadraticForms.lean) defines chi-square, Student-t, and F probability laws from independent variables; `normal_matrix_quadratic_form` proves the chi-square law for symmetric idempotent matrices, with matrix rank as degrees of freedom; [GaussianMahalanobis](../LectureNotes/GaussianMahalanobis.lean): `normal_mahalanobis` proves the covariance-inverse form for the actual multivariate Gaussian with positive definite covariance | [GaussianBlockConditioning](../LectureNotes/GaussianBlockConditioning.lean) proves the full conditional block-normal formula, with positive definite conditioning block and possibly singular residual covariance. [StudentTIntegrability](../LectureNotes/StudentTIntegrability.lean) and [StudentTMoments](../LectureNotes/StudentTMoments.lean) prove exact L1/L2 thresholds and the mean/variance formulas. [UniformSquare](../LectureNotes/UniformSquare.lean) proves the square-of-uniform density and CDF; [DensityTransform](../LectureNotes/DensityTransform.lean) proves one-dimensional density change of variables with explicit invertibility and nonzero-derivative conditions. General conditional density and PMF formulas are now proved in ConditionalDensities and ConditionalDensityLaws, as detailed below. [GaussianConditioning](../LectureNotes/GaussianConditioning.lean) proves the scalar jointly Gaussian conditional law with regression coefficient and Schur-complement variance, requiring positive conditioning variance. |
| L2 statistics and simulation | Measurable statistic/estimator types, integral-based unbiasedness; sample mean, sample variance, unbiased sample-variance lemma; finite population and Horvitz–Thompson calculations; [NormalFStatistic](../LectureNotes/NormalFStatistic.lean): `normal_fStatistic` proves the law of the sample-variance ratio divided by the population-variance ratio for two independent normal samples; [UniformEndpoint](../LectureNotes/UniformEndpoint.lean) identifies the standardized uniform sample maximum with a Beta law and derives its exact moments | [OrderStatistics](../LectureNotes/OrderStatistics.lean) constructs the measurable sorted sample, including ties. [EmpiricalQuantiles](../LectureNotes/EmpiricalQuantiles.lean) proves the exact generalized-inverse empirical quantile rank `ceiling(n*q)` for interior q. [MonteCarlo](../LectureNotes/MonteCarlo.lean) proves IID simulation-statistic laws, strong consistency of means, event frequencies and sample variances, and measurable empirical-quantile consistency under an explicit crossing condition. Convolution densities, shifted lognormal simulation and illustrative statistics are now proved as detailed below. |
| L3 convergence and stochastic order | Almost-sure, probability, distribution, mean, mean-square convergence; consistency and Gaussian asymptotic normality with a canonical target law, measurable estimators, and eventually nonzero rates; `StochasticLittleO`, `StochasticBigO` with nonzero scales and the uniform-in-n tail bound; [StochasticOrder](../LectureNotes/StochasticOrder.lean) proves weak convergence implies stochastic boundedness, op implies Op, addition/product rules, Op times op, and vanishing-scale rules; [CDFConvergence](../LectureNotes/CDFConvergence.lean) proves equivalence between Mathlib weak convergence and convergence of CDFs at every continuity point of the limiting CDF, including discrete and mixed limits | [StochasticPowers](../LectureNotes/StochasticPowers.lean) proves the power-scale rules, the Gaussian growing-variance example, and the explicit Chebyshev stochastic bound with positive variance. [AlternatingUniform](../LectureNotes/AlternatingUniform.lean) proves the exact alternating-uniform sequence is uniformly stochastically bounded but has no weak limit. [StochasticSampleMean](../LectureNotes/StochasticSampleMean.lean) proves the inverse-square-root sample-mean rate with only common first/second moments and pairwise independence within rows, including zero variance. |
| L4 bootstrap | `BootstrapIndex`, `bootstrapSample`; [Bootstrap](../LectureNotes/Bootstrap.lean) defines the empirical probability law, proves its CDF equals the empirical CDF, and proves independent uniform index draws have the IID empirical sampling law; [BootstrapMoments](../LectureNotes/BootstrapMoments.lean) proves the empirical-law integral, its variance, and the bootstrap mean's exact conditional mean/variance. Empirical variance is strongly consistent under finite second moments | [BootstrapConditionalCLT](../LectureNotes/BootstrapConditionalCLT.lean) derives the actual conditional sample-mean CLT and quantile convergence from finite second moments and positive variance. [BootstrapMeanIntervals](../LectureNotes/BootstrapMeanIntervals.lean) proves the resulting basic interval coverage, using the exact conditional quantiles. [BootstrapStudentizedAsymptotics](../LectureNotes/BootstrapStudentizedAsymptotics.lean) and [BootstrapStudentizedIntervals](../LectureNotes/BootstrapStudentizedIntervals.lean) derive actual bootstrap-t uniform CDF/quantile limits and interval coverage under finite fourth moments. Zero sample and resample variances are controlled probabilistically. [BootstrapMaximum](../LectureNotes/BootstrapMaximum.lean) proves a persistent conditional atom at the observed maximum and a CDF discrepancy of at least one half from the true uniform endpoint error for every nonempty sample. Actual nonlinear mean/variance bootstrap and joint sample-size/simulation-budget limits are proved in the new-notes ledger. ParametricNormalBootstrap and ParametricNormalBootstrapLimits derive the fitted-normal mean bootstrap and its conditional CDF/quantile limits; ParametricUniformBootstrap proves an exact normalized endpoint pivot. |
| L5 risk and examples | MSE/bias/variance, exact shrinkage risk, normalized `ExponentialFamily` and the separate algebraic `HasExponentialForm`, exponential-family factorization, general dominated sufficiency and likelihood-ratio minimality criteria; [NormalVarianceRisk](../LectureNotes/NormalVarianceRisk.lean) proves Example 5's sample-variance variance, both estimator MSEs, empirical-variance bias, and strict risk improvement for `n > 1` and positive variance; [UniformSufficiency](../LectureNotes/UniformSufficiency.lean) proves sufficiency of the maximum for the positive uniform endpoint family and of both extremes for the translated unit interval, using their actual product measures and parameter-dependent supports. [VarianceAsymptotics](../LectureNotes/VarianceAsymptotics.lean) proves strong consistency of the denominator-n−1 sample variance under finite second moments, and its square-root-n CLT under a finite fourth central moment, with limiting variance `μ₄−σ⁴`. Translated-uniform and triangular-endpoint minimality are proved as described above; [GumbelSufficiency](../LectureNotes/GumbelSufficiency.lean) proves sufficiency/minimality of the sum of exp(−X), and [CauchySufficiency](../LectureNotes/CauchySufficiency.lean) proves minimality of the full ordered sample for the actual Cauchy location family, including ties. [UnbiasedNonexistence](../LectureNotes/UnbiasedNonexistence.lean) proves that no real estimator on the actual fixed-size Bernoulli experiment can be unbiased for 1/p over all interior p | [BinomialTwoSufficiency](../LectureNotes/BinomialTwoSufficiency.lean) constructs the actual Binomial(2,p) product experiment for all p in [0,1], including endpoints, and proves sum sufficiency and minimality. [WeightedEstimators](../LectureNotes/WeightedEstimators.lean) proves the weighted mean, variance, MSE, unique unit-sum minimum and unique oracle MSE minimum. [ShrinkageImprovement](../LectureNotes/ShrinkageImprovement.lean) proves the exact improving coefficient interval. [RandomizedExperiment](../LectureNotes/RandomizedExperiment.lean) derives design-unbiased ATE estimation from actual uniform fixed-size assignment; [Skewness](../LectureNotes/Skewness.lean) retains the source's n−1 variance convention. [BinomialSample](../LectureNotes/BinomialSample.lean), [BinomialConditioning](../LectureNotes/BinomialConditioning.lean), [BinomialRaoBlackwell](../LectureNotes/BinomialRaoBlackwell.lean) and [BinomialMinimal](../LectureNotes/BinomialMinimal.lean) prove the general Binomial(k,p) counting example, conditional estimator, unbiasedness, risk reduction and minimality including boundary parameters. The unrestricted pointwise minimality criterion is false for arbitrary density versions; the checked counterexample is documented below. |
| L6 estimation methods | Likelihood, log-likelihood, score, Fisher information, MLE, moment equation; log-likelihood comparison, score derivative, interior-MLE score condition; regular density model and information results; [BernoulliModel](../LectureNotes/BernoulliModel.lean) constructs a regular Bernoulli family and proves its exponential representation, actual score, Fisher information `1/(p*(1-p))`, unbiasedness, and application of the unbiased Cramér–Rao bound for `0 < p < 1`; [NormalLikelihoodRatio](../LectureNotes/NormalLikelihoodRatio.lean) proves the unique normal mean MLE with known unit variance; [NormalUnknownVarianceMLE](../LectureNotes/NormalUnknownVarianceMLE.lean) proves the joint mean/variance maximum for positive empirical variance, strict nonexistence when that variance is zero, and almost-sure existence under nondegenerate IID normals with n>1; [UniformEndpoint](../LectureNotes/UniformEndpoint.lean) proves the uniform endpoint MLE and its nonregular limit; [BoundaryNormalMLE](../LectureNotes/BoundaryNormalMLE.lean) and [NeymanScott](../LectureNotes/NeymanScott.lean) give the boundary and incidental-parameter examples. [MethodOfMoments](../LectureNotes/MethodOfMoments.lean) proves scalar inverse-moment strong consistency and derives its delta-method limit from the IID CLT, plus the exact normal and both exponential moment equations. [InstrumentalVariables](../LectureNotes/InstrumentalVariables.lean) proves identification from the actual residual moments, the unique empirical moment solution, and strong covariance/slope consistency under finite second moments and instrument relevance | [BinaryInstrument](../LectureNotes/BinaryInstrument.lean) derives the binary-instrument covariance factorization, exact ratio of group mean differences, and relevance equivalence with both groups nonempty. [CausalIdentification](../LectureNotes/CausalIdentification.lean) proves the observable conditional-means ATE formula from actual conditional independence, overlap and outcome consistency. [VectorMethodOfMoments](../LectureNotes/VectorMethodOfMoments.lean) derives vector inverse-moment consistency and the Gaussian delta-method limit, including singular limiting covariance. The explicit uniform-endpoint Cramér–Rao counterexample is tracked below. |

The formal proofs sometimes use stronger Mathlib results instead of reproducing
the source proof line by line. In particular, SLLN, scalar CLT, Jensen, Hölder,
and Gaussian independence are checked applications of library theorems. The
source's invalid mean-value witness step in the delta-method proof is replaced
by its explicit divided-difference argument.

The Gaussian sampling proofs use the notes' centering projection. Its rank,
Gaussian image law, and independence from the sample mean are all proved.
The fourth standard-normal moment is derived by differentiating the known
moment-generating function; it is not supplied as a hypothesis of the risk results.


## Further completed definitions and examples

[JointDistributions](../LectureNotes/JointDistributions.lean),
[ConditionalDensities](../LectureNotes/ConditionalDensities.lean), and
[ConditionalDensityLaws](../LectureNotes/ConditionalDensityLaws.lean) prove L1's
joint CDF, marginal CDF limits, density marginalization, discrete marginal sums,
positive-atom conditioning, and actual conditional density ratios marginal-almost
everywhere. [DensityDerivatives](../LectureNotes/DensityDerivatives.lean) proves
the univariate and mixed CDF derivative formulas under sufficient continuity and
domination. [BinomialSum](../LectureNotes/BinomialSum.lean) identifies the actual
IID Bernoulli sum with the binomial law, including empty sums and boundary
parameters, and connects the finite count-space model to Mathlib's law.

The actual one-sample and two-sample t asymptotics, nonlinear mean/variance
sampling CLT, and conditional variance bootstrap are tracked in the new-notes
ledger. The additional sampling and sufficiency examples are now covered below.


## Additional sampling and sufficiency examples

- `SamplingDensities` proves convolution and repeated-sum densities for the
  actual independent sampling laws, including the sample-mean Jacobian.
  `ShiftedLognormal` proves the displayed positive-variance density is the
  shifted exponential Gaussian pushforward, and proves the IID simulation and
  sample-mean laws.
- `SurveySampling` constructs the independent Bernoulli inclusion design,
  proves its Horvitz–Thompson variance and unbiased variance estimator, and
  proves the general pair-inclusion variance estimator with positive pair
  probabilities explicitly required. It connects equal inclusion probabilities
  to the simple-random-sampling mean and finite-population correction.
- `SamplingStatistics` formalizes all three coin statistics and the exact
  ten-flip example, the lower empirical median with ceiling rank, and an
  integer-trimmed sample mean. The median convention is explicit; the source's
  informal “n/2-th highest” does not uniquely specify all sample sizes.
- `NormalJointSufficiency` proves sufficiency of the raw-moment pair and of
  (mean, n−1 variance) in the actual positive-variance normal experiment. It
  also proves the fixed-design regression sufficient pair with no rank
  assumption. `SufficiencyObstruction` and `NormalJointInsufficiency` prove
  that the mean alone is insufficient when both parameters vary and n>1.
- `PointwiseMinimalityCounterexample` uses two positive density versions of
  the same Gaussian law. Their pointwise likelihood ratios recover the
  indicator of a null singleton, while a constant sufficient statistic cannot
  recover it pointwise. Almost-sure minimality avoids this defect. This does
  not refute the correctly stated almost-sure recovery theorems.

## Bias correction and additional source examples

- `BootstrapBias` proves the exact quadratic sampling bias and conditional
  bootstrap bias, the residual bias a·v/n² after ordinary bootstrap correction,
  and the exactly unbiased correction using the n−1 sample variance.
- `FourthMomentSums` proves the exact fourth central moment of an independent
  sample mean from finite fourth moments. `BootstrapTaylorBias` derives a
  second-order expectation expansion from actual C³ regularity and a bounded
  third derivative, with the expected absolute-cubic remainder controlled
  using second and fourth moments. A probabilistic remainder is not integrated
  without justification.
- `MonteCarloBias` proves exact simulation MSE and a variance-sensitive
  Lipschitz bound. `MonteCarloBiasJoint` transfers the scaled error result to
  actual observations and independent uniform resampling indices. For this
  bias-scale result, n/B(n)→0 is required; the first-order interval result
  requires only B(n)→∞.
- `ClassifierConcentration` formalizes the individual and simultaneous
  classifier-accuracy guarantees, the logarithmic sample-size formula, and
  the printed 26,492-observation guarantee with certified rational bounds.
  Classifiers may share their test set and need not be independent of each other.
- `ProbabilityExamples` gives the exact employment-count event {4,…,10}, the
  measurable nonnegative-income band, and sigma-algebra closure consequences.


- `BootstrapBiasAsymptotics` derives the actual finite-fourth-moment sampling
  and conditional bias expansions under C³ smoothness and a bounded third
  derivative; n times the difference between exact bootstrap bias and sampling
  bias tends to zero almost surely. `BootstrapBiasMonteCarloAsymptotics` gives
  the simulated version: the n-scaled error tends to zero in probability
  under the actual joint data/index law when the transform is also Lipschitz
  and n/B→0.
- `BootstrapBiasCorrection` separately proves that the expected bias of the
  exact corrected estimator is o(1/n), under bounded IID observations,
  C³ smoothness and bounded second and third derivatives. It establishes integrability and
  domination explicitly; this conclusion is not inferred from an almost-sure
  estimate of the sampling bias.
- `BernsteinAnalytic` and `Bernstein` prove the displayed variance-sensitive
  inequality, including its exact 2/3 range constant and zero-variance case,
  from the exponential series, independence and Chernoff optimization.
- `SquaredMeanDelta` specializes the actual IID sample-mean delta method to
  the square, with variance 4μ²v and the explicitly degenerate zero-mean limit.
  `NormalMeanInformation` derives both information identities from the actual
  known-variance normal location density and its derivatives.
- `UniformCramerRaoCounterexample` proves the corrected maximum's
  unbiasedness and variance, the failure of both information identities,
  and the actual full-sample squared-score information N²/θ². The regular
  additivity expression N/θ² printed in the source does not hold in this model.

- `BernoulliSampleInformation` and `BernoulliCramerRao` complete L6 Example 8
  for the actual full Bernoulli sample. They derive the finite-sum score
  identity and information, prove the lower bound for arbitrary estimators
  unbiased over the model, and prove that the sample mean is UMVU, including
  the degenerate endpoints.

## Simulation and bias: distinct conclusions

| Quantity | Proved conclusion | Replication requirement |
| --- | --- | --- |
| Conditional simulated bias | Its expectation equals the exact conditional bootstrap bias, when integrable. | Every positive finite B. |
| Expected bias of the simulated corrected estimator | It equals the exact correction's expected bias and is o(1/n) under bounded IID observations, C³ smoothness and bounded second/third derivatives. | Any positive B(n), including constant B. |
| Error in estimating bias at the 1/n scale | n times the Monte Carlo error tends to zero in probability under the joint data/index law, with the stated Lipschitz and moment hypotheses. | n/B(n)→0. |
| First-order simulated basic or bootstrap-t intervals | Actual joint sampling/resampling coverage tends to the nominal level under the corresponding sampling and smoothness/moment conditions. | B(n)→∞. |

The expectation identities and integrability justification are in
`MonteCarloBiasExpectation`. A small expected bias does not by itself imply
small simulation variance or accurately estimated critical values.
