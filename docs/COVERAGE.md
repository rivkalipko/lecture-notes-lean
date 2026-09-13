# Coverage ledger

The project is incomplete. This ledger covers all **32 numbered theorems** in
Lectures 1–6, followed by definitions and other material. A row marked
**restricted** does not count as a proof of the general source statement.
Statements marked **proved** include the explicit measurability, integrability,
nonzero-denominator, and regularity hypotheses described below and in
[SOURCE_AUDIT.md](SOURCE_AUDIT.md).

Declaration names are in the `LectureNotes` namespace except where a nested
namespace is shown. The files linked below are all imported by `LectureNotes.lean`.

## Numbered theorems

| Source | Status | Formal declarations and qualifications |
| --- | --- | --- |
| L1 T1, probability laws | Proved | [Foundations](../LectureNotes/Foundations.lean): `prob_empty`, `prob_univ`, `prob_compl`, `prob_mono`, `prob_bounds`, `inclusion_exclusion`, `union_bound`. Derived from Mathlib measures. |
| L1 T2, continuity of probability | Proved | [ProbabilityLaws](../LectureNotes/ProbabilityLaws.lean): `probability_continuous_from_below`, `probability_continuous_from_above`. |
| L1 T3, conditional probability | Proved for finite partitions | `multiplication_rule`, `total_probability` in ProbabilityLaws; `conditional_probability`, `bayes` in Foundations. Conditioning denominators are nonzero. |
| L1 T4, expectation and variance | Proved | Foundations: `expectation_const`, `expectation_linear`, `variance_eq_second_moment_sub_mean_sq`, `variance_scale`, `variance_translate`. Integrable or square-integrable variables as appropriate. |
| L1 T5, iterated expectations | Proved | [ConditionalExpectation](../LectureNotes/ConditionalExpectation.lean): `iterated_expectations`, using Mathlib's conditional expectation on a sub-sigma-algebra. |
| L1 T6, best predictor | Proved for square-integrable competitors | `conditional_expectation_best_predictor` proves squared-loss optimality using an orthogonal decomposition. Real integrals are used, so infinite-loss competitors are excluded explicitly. |
| L2 T1, normal sampling | Proved | [NormalSampling](../LectureNotes/NormalSampling.lean): `normal_sampleMean`, `normal_sampleMean_independent_sampleVariance`. [NormalSamplingDistribution](../LectureNotes/NormalSamplingDistribution.lean): `normal_sampleVariance`, `normal_studentized_mean`. The last two require `n > 1` and positive population variance. `residualSpace_projection` and `residualSpace_finrank` prove the centering projection and its dimension `n - 1`. |
| L2 T2, finite population | Proved | [FinitePopulation](../LectureNotes/FinitePopulation.lean): `simpleRandomSampling_mean`, `simpleRandomSampling_variance`. The probability model is uniform on all n-element subsets; marginal/pair inclusion probabilities are proved by counting. Assumes `0 < n ≤ N` and `1 < N` for the variance formula. |
| L2 T3, Horvitz–Thompson | Proved | [SamplingMoments](../LectureNotes/SamplingMoments.lean): `horvitzThompson_unbiased`, `horvitzThompson_variance`. Inclusion quantities are actual expectations. The algebra holds more generally for integrable/square-integrable random weights; selection indicators in FinitePopulation give the sampling interpretation. |
| L3 T1, Jensen | Proved | [Inequalities](../LectureNotes/Inequalities.lean): `jensen_inequality`, from Mathlib Jensen, with integrability of both the variable and convex transform. |
| L3 T2, Markov | Proved | `markov_inequality`, nonnegative integrable random variable and positive threshold. |
| L3 T3, Chebyshev | Proved | `chebyshev_deviation`, with the actual absolute-deviation event; `chebyshev_inequality` also gives the squared-deviation form. |
| L3 T4, Hölder | Proved | `holder_absolute`, for arbitrary signs using absolute values; `holder_inequality` gives the nonnegative form. |
| L3 T5, Hoeffding | Proved | [Concentration](../LectureNotes/Concentration.lean): `hoeffding_lemma`, `hoeffding_sum`, `hoeffding_sampleMean`. Independent observations suffice. The displayed sample-mean bound has exponent `-2*n*epsilon^2/(b-a)^2`, with `a < b`. |
| L3 T6, Cramér–Wold | Proved | [CramerWold](../LectureNotes/CramerWold.lean): `cramer_wold`, in finite-dimensional real inner-product spaces. Reverse direction uses characteristic functions and Lévy's theorem. |
| L3 T7, convergence implications | Proved | [Convergence](../LectureNotes/Convergence.lean): all five implications are separate theorems. Mean and mean-square convergence include integrability hypotheses. |
| L3 T8, Slutsky | Proved | `slutsky_add`, `slutsky_mul`, `slutsky_div`; division requires a nonzero limiting constant. |
| L3 T9, continuous mapping | Proved | `continuous_mapping_almost_sure`, `continuous_mapping_probability`, `continuous_mapping_distribution`; mapping at a constant limit also has a theorem requiring continuity only there. |
| L3 T10, Chebyshev WLLN | Proved | [WeakLaw](../LectureNotes/WeakLaw.lean): `weak_law_uncorrelated`. Derives the variance of the centered sample mean and convergence from the source's `n^-2 sum variance -> 0` condition. |
| L3 T11, SLLN | Proved via Mathlib | [LargeSample](../LectureNotes/LargeSample.lean): `strong_law_of_large_numbers`; pairwise independence and identical laws suffice. |
| L3 T12, CLT | Proved via Mathlib and Cramér–Wold | LargeSample: `central_limit_theorem`; [MultivariateCLT](../LectureNotes/MultivariateCLT.lean): `multivariate_central_limit_theorem`. The multivariate target is specified by its Gaussian projection laws with matching variances. Construction of a target random variable from a covariance matrix is not provided here. |
| L3 T13, Lindeberg–Feller | **Missing** | The independent, non-identically-distributed limit theorem and its Lindeberg condition have not been formalized. The IID CLT is not a substitute. |
| L3 T14, delta method | Proved | [DeltaMethod](../LectureNotes/DeltaMethod.lean): `delta_method`, `delta_method_normal`. Uses the measurable divided difference, the exact `sqrt n` rate, and proves the transformed Gaussian variance. Global continuity and differentiability at the limit suffice; a zero derivative is allowed and gives a degenerate limit. |
| L4 T1, empirical CDF | Proved | [EmpiricalDistribution](../LectureNotes/EmpiricalDistribution.lean): `empiricalCDF_unbiased`, `empiricalCDF_variance`, `empiricalCDF_consistency`, `empiricalCDF_strong_consistency`. These are pointwise statements for each fixed threshold. |
| L4 T2, Glivenko–Cantelli / DKW | **Missing** | Neither the uniform convergence theorem nor the sharp uniform exponential inequality is proved. `empiricalCDF_pointwise_concentration` is explicitly only a pointwise bound. |
| L5 T1, MSE decomposition | Proved | Foundations: `mse_eq_variance_add_bias_sq`; Estimation: `mse_bias_variance_decomposition`. Squared-error expectation is a genuine integral, not an assumed calculation. |
| L5 T2, factorization | **Restricted** | [Sufficiency](../LectureNotes/Sufficiency.lean): `finite_factorization_iff`, for a finite sample space and strictly positive common support. Sufficiency is defined by parameter-independent conditional masses. General dominated continuous models remain missing. |
| L5 T3, exponential family statistic | **Restricted** | [Estimation](../LectureNotes/Estimation.lean): `exponential_family_factorizes_sum` states and proves the product factorization through the explicitly given summed statistic. Sufficiency: `finite_exponential_family_sum_sufficient` supplies the sufficiency conclusion for the finite positive-support case. |
| L5 T4, minimal sufficiency | **Restricted** | Sufficiency: `finite_minimal_sufficiency`, with the likelihood-ratio criterion proved in both directions for finite strictly positive models. Models with parameter-dependent support, including the uniform examples, remain missing. |
| L5 T5, Rao–Blackwell | **Partial** | ConditionalExpectation: `rao_blackwell_mean`, `rao_blackwell_mse`, and best-predictor optimality. These prove unbiasedness and risk reduction for conditional expectation under each probability measure. The general sufficiency argument producing one parameter-independent estimator has not been formalized. |
| L6 T1, information equalities | Proved under explicit corrected regularity | [RegularDensity](../LectureNotes/RegularDensity.lean): `RegularDensity.first_information_equality`, `second_information_equality`, `score_is_log_derivative`, `logHessian_is_score_derivative`. Normalization is differentiated twice using integrable bounds on density derivatives. [RegularCramerRao](../LectureNotes/RegularCramerRao.lean) connects weighted integrals to the actual probability model. |
| L6 T2, Cramér–Rao | Proved under explicit corrected regularity | RegularCramerRao: `RegularDensity.cramer_rao` proves the bound from a density model, including differentiation of the estimator's expectation. [Information](../LectureNotes/Information.lean): `cramer_rao_bound`, `cramer_rao_unbiased`, `fisherInformation_sum` isolate the covariance argument and information additivity. |

## Definitions and other material

| Material | Present | Still missing or restricted |
| --- | --- | --- |
| L1 probability foundations | Mathlib `MeasurableSpace`, `Measure`, `IsProbabilityMeasure`; measurable `Event` and `RandomVariable`; conditional, pairwise, joint, and conditional independence of events; `cdfOf` with probability interpretation, monotonicity, limits, and right continuity | Not every elementary set-theoretic example is transcribed. |
| L1 moments and covariance | Integral expectation, variance, covariance identities, independence implies zero covariance, zero variance implies constancy almost everywhere, covariance Cauchy–Schwarz bound; [ChiSquaredMoments](../LectureNotes/ChiSquaredMoments.lean) proves the fourth standard-normal moment and chi-square mean/variance with square integrability | Correlation equality characterization; remaining distribution-specific moment tables and examples. |
| L1 distribution theory | Normal laws through Mathlib; [GaussianQuadraticForms](../LectureNotes/GaussianQuadraticForms.lean) defines chi-square, Student-t, and F probability laws from independent variables; `normal_matrix_quadratic_form` proves the chi-square law for symmetric idempotent matrices, with matrix rank as degrees of freedom; [GaussianMahalanobis](../LectureNotes/GaussianMahalanobis.lean): `normal_mahalanobis` proves the covariance-inverse form for the actual multivariate Gaussian with positive definite covariance | Remaining distribution catalog, density/CDF transformations, conditional multivariate-normal formulas, and Student-t moment existence/formulas. |
| L2 statistics and simulation | Measurable statistic/estimator types, integral-based unbiasedness; sample mean, sample variance, unbiased sample-variance lemma; finite population and Horvitz–Thompson calculations; [NormalFStatistic](../LectureNotes/NormalFStatistic.lean): `normal_fStatistic` proves the law of the sample-variance ratio divided by the population-variance ratio for two independent normal samples | General sampling-distribution examples, Monte Carlo algorithms, empirical quantile/order-statistic proofs. |
| L3 convergence and stochastic order | Almost-sure, probability, distribution, mean, mean-square convergence; consistency and Gaussian asymptotic normality; `StochasticLittleO`, `StochasticBigO` with nonzero scales and the uniform-in-n tail bound; [StochasticOrder](../LectureNotes/StochasticOrder.lean) proves weak convergence implies stochastic boundedness, op implies Op, addition/product rules, Op times op, and vanishing-scale rules | The bridge between the source's CDF definition of weak convergence and Mathlib's weak topology; specializations to power scales and the remaining examples. |
| L4 bootstrap | `BootstrapIndex`, `bootstrapSample`; [Bootstrap](../LectureNotes/Bootstrap.lean) defines the empirical probability law, proves its CDF equals the empirical CDF, and proves independent uniform index draws have the IID empirical sampling law | Bootstrap quantile algorithms and validity theorems. |
| L5 risk and examples | MSE/bias/variance, exact shrinkage risk, exponential-family factorization, finite positive sufficiency and minimal sufficiency; [NormalVarianceRisk](../LectureNotes/NormalVarianceRisk.lean) proves Example 5's sample-variance variance, both estimator MSEs, empirical-variance bias, and strict risk improvement for `n > 1` and positive variance | General loss/risk decision theory; remaining strict risk comparisons; fourth-moment CLT examples; concrete sufficient/minimal statistics and Rao–Blackwell counting examples. |
| L6 estimation methods | Likelihood, log-likelihood, score, Fisher information, MLE, moment equation; log-likelihood comparison, score derivative, interior-MLE score condition; regular density model and information results | Concrete normal/uniform MLE calculations, identification examples, all method-of-moments examples and nonregular counterexamples. |

The formal proofs sometimes use stronger Mathlib results instead of reproducing
the source proof line by line. In particular, SLLN, scalar CLT, Jensen, Hölder,
and Gaussian independence are checked applications of library theorems. The
source's invalid mean-value witness step in the delta-method proof is replaced
by its explicit divided-difference argument.

The Gaussian sampling proofs use the notes' centering projection. Its rank,
Gaussian image law, and independence from the sample mean are all proved.
The fourth standard-normal moment is derived by differentiating the known
moment-generating function; it is not supplied as a hypothesis of the risk results.
