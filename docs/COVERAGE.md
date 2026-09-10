# Coverage ledger

This ledger is part of the transcription record.  “Formalized” means that a
Lean declaration with explicit hypotheses is present and checked.  The audit
column points to the reason a source statement is deferred or restricted.

| Notes | Material | Lean coverage |
| --- | --- | --- |
| L1 | Probability-space axioms and finite probability laws | `Foundations.ProbabilitySpace`; empty, universal, complement, bounds, monotonicity, inclusion-exclusion algebra, and conditional-probability ratio |
| L1 | Expectation, variance, covariance, bias, MSE | `Foundations.Expectation`; linearity interface and checked variance/MSE identities |
| L1 | Conditional expectation, independence, CDF transformations, normal quadratic forms | Deferred; see the corresponding L1 entries in `SOURCE_AUDIT.md` for measurability, a.e., inverse-map, and matrix hypotheses |
| L2 | Statistic and estimator terminology | `Estimation.Statistic`, `Estimation.Estimator`, `Estimation.Unbiased` |
| L2 | Sample mean and sample-variance algebra | `Sampling.sampleMean`, `sum_centered_sq`, `sample_variance_identity` |
| L2 | IID normal sampling distributions and finite-population/Horvitz–Thompson calculations | Deferred; these require a concrete probability model and finite-population design definitions |
| L2/L4 | Empirical CDF and bootstrap resampling | `LargeSample.empiricalCDF`, its nonnegativity/monotonicity/unit bound, and `bootstrapSample` |
| L3 | Markov, Hölder, and Chebyshev | `Inequalities.markov_inequality`, `holder_inequality`, and `chebyshev_inequality` |
| L3 | Almost-sure, in-probability, in-distribution, mean, and mean-square convergence | `LargeSample.ConvergesAlmostSurely`, `ConvergesInProbability`, `ConvergesInDistribution`, `ConvergesInMean`, `ConvergesInMeanSquare` |
| L3 | Strong law and central limit theorem | `LargeSample.strong_law_of_large_numbers` and `central_limit_theorem`, delegating to Mathlib with the required integrability/independence laws |
| L3 | Jensen, Hoeffding, Slutsky, continuous mapping, delta-method details | Deferred; source statements need additional measurable-function and moment infrastructure |
| L5 | MSE/bias/variance and shrinkage comparisons | `Foundations.Expectation.mse_eq_variance_add_bias_sq` and `Estimation.shrinkage_mse` |
| L5 | Exponential-family factorization | `Estimation.ExponentialFamily` and `exponential_family_sample_factorization` |
| L5 | Sufficiency and minimal sufficiency | `Estimation.factorizesThrough` is available; the general continuous-data factorization proof is deliberately deferred (see audit) |
| L5 | Rao–Blackwell | Deferred until conditional expectation is represented as an a.e.-defined object |
| L6 | Likelihood, log-likelihood, score, Fisher information, MLE, moments | `EstimationTheory` definitions |
| L6 | Log-score derivative, interior-MLE score condition, log-MLE equivalence | `score_eq_deriv_log_likelihood`, `score_zero_at_interior_mle`, and `log_likelihood_preserves_mle` |
| L6 | Information equalities and Cramér–Rao | Deferred; differentiation under the integral and positivity/finite-information hypotheses must be encoded first |

The source PDFs remain in the repository so that every deferred row can be
extended without losing the original reference material.
