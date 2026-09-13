# Source audit

Sources: the six original `Lecture*_Notes.pdf` files, MIT 14.380,
Statistical Methods in Economics, Fall 2026. Page numbers below are printed PDF
page numbers. The PDFs are preserved unchanged. Compilation checks proofs of
formal statements; it does **not** by itself check that those statements match
the source. The coverage ledger separately records that obligation.

## Conventions needed for rigorous statements

* Random variables and transformations must be measurable. Expectations used
  in linearity require integrability; variance/covariance identities require
  square integrability. Lean's real-valued integral is totalized at zero on
  nonintegrable functions, so omitting these hypotheses can change meaning.
* General measures take values in the extended nonnegative reals. Finite
  probabilities can also be expressed as real numbers. The codomain `R` in
  Lecture 1 Definition 2 excludes the infinite measures discussed immediately
  afterward.
* Sample means require a positive sample size; unbiased sample variance and
  normal t-statistics require at least two observations. Nondegenerate normal
  density and standardized distribution formulas require positive variance.
* Conditional probability ratios require positive denominator probability.
  Product definitions of independence remain meaningful for null events.
* Conditional expectations are defined up to almost-everywhere equality.
  Equalities of random variables inferred from moments hold almost surely,
  not necessarily at every outcome.
* Infinite losses require an extended nonnegative integral. Real-valued squared
  loss comparisons in this project explicitly impose square integrability on
  both the response and competing predictor.

## Specific issues and qualifications

| Source | Issue / treatment needed |
| --- | --- |
| L1 p3, Theorem 3 | Add positivity of every conditioning event used in the multiplication, total-probability, and Bayes formulas. |
| L1 p3, Definition 5 | Conditional-probability characterization of independence needs both event probabilities positive; the product characterization does not. |
| L1 p5, density derivative | The identity `F' = f` holds at appropriate continuity points of a density, or almost everywhere under the corresponding hypotheses. It does not hold everywhere for an arbitrary density version. |
| L1 p5, inverse transformation | A strictly increasing continuously differentiable map need not have a differentiable inverse: `g(x)=x^3` at zero is a counterexample. The inverse derivative formula needs a nonzero derivative. |
| L1 pp5–6, square of uniform | The transformed density is `1/(2 sqrt y)` on `0<y<1`, up to endpoint choices. The set where a chosen density is positive and its topological support are different notions. |
| L1 p9, Student t | The mean is zero only for degrees of freedom greater than one. At one degree of freedom the mean does not exist. The variance formula requires degrees of freedom greater than two; do not encode nonexistence as a finite real-valued variance. Visually verified. |
| L1 p10, mixed CDF derivative | Continuity of the joint CDF alone is insufficient to recover a density by mixed differentiation. |
| L1 pp11–12, best predictor | Require measurable competing predictors and use extended loss, or restrict the real-valued result to square-integrable competitors. |
| L1 p13, covariance bound proof | Division by `V(Y)` needs a separate zero-variance case. Correlation requires nonzero variances and perfect correlation implies affine dependence almost surely. |
| L1 p15, quadratic forms | The chi-square conclusion requires a symmetric idempotent matrix (an orthogonal projection), not merely an arbitrary idempotent matrix. |
| L2 p3, sampling without replacement | Ordered simple random draws are identically distributed, though generally dependent. The statement "nor identically distributed" is incorrect. |
| L2 p6, Monte Carlo quantile | For the generalized inverse empirical quantile and one-based order statistics, use `ceil(alpha*B)`, not `floor(alpha*B)`. The latter can be zero. |
| L2 p9, indicator covariance | Strict negativity requires `0<n<N` and `N>1`; at a census covariance is zero. |
| L2 p10, finite population comparison | The variance of one independent draw from the finite population is `(N-1)/N * S^2`, not exactly `S^2`. Also `n/N -> 0` alone is insufficient for an absolute variance difference to vanish if population variances grow without bound. |
| L2 p11, variance estimation remark | Unbiased inverse-probability estimation of pair terms requires positive pair inclusion probabilities for those terms, not just positive marginal inclusion probabilities. |
| L3 p1, Jensen | Require integrability of the random variable and its convex transform for a real-valued result. |
| L3 pp2–3, Hoeffding | Specify `a<b` when dividing by `(b-a)^2`; a degenerate interval can instead be treated separately. |
| L3 pp4–9, convergence and order | Require measurable random variables and nonzero deterministic scale sequences. The deterministic big-O definition needs an absolute value/bound on absolute ratios. |
| L3 p10, Example 2 | The last conclusion should be `X_n/n -> 0` in mean square, not `X_n -> 0`, when `X_n ~ N(0,n)`. |
| L3 p10, Example 3 | Standardization by `sqrt(V(Y_n))` needs positive variances, or separate zero-variance cases. |
| L3 p12, Lindeberg–Feller | Standard deviations `c_n` must be positive eventually; otherwise the normalizing ratios are undefined in the mathematical statement. |
| L3 pp12–13, delta proof | Arbitrary mean-value witnesses need not be measurable. The explicit remainder proof avoids this gap and only needs differentiability at the limiting point. |
| L4 p2, DKW | The PDF **does contain absolute-value bars** around the CDF difference. Text extraction dropped them. This is a transcription hazard, not a source error. Visually verified. |
| L4 p3, bootstrap quantile | Same floor/ceiling correction as L2 p6. Bootstrap consistency needs conditions on the statistic, not just pointwise or uniform CDF convergence. |
| L5 p2, nonlinear bias | Nonlinearity does not always imply bias (for example a cubic transform of a symmetric mean-zero variable). The claim is a generic possibility, not a universal implication. |
| L5 p2, bias expansion | An `o_p(1/n)` Taylor remainder cannot automatically be replaced by an `o(1/n)` expectation. Additional moment/uniform-integrability control and simulation-error conditions on `B` are needed. |
| L5 p4, variance MSE comparison | The comparison assumes `n>1` and positive population variance for strict inequality; at zero variance both MSEs are zero. |
| L5 p5, shrinkage | Strict improvement from small shrinkage requires positive initial variance. Pointwise improvement need not give a single uniformly improving shrinkage amount from boundedness of the parameter set alone. |
| L5 pp5–6, weights | The unbiasedness "iff" is a statement over all possible means, not at a fixed zero mean. Strict convexity and the displayed strict shrinkage claims require positive variance, with an endpoint case when the mean is zero. |
| L5 p7, variance asymptotic normality | Requires a finite fourth central moment, stronger than merely finite variance. |
| L5 pp8–9, factorization proof | For continuous data, the conditional law on a statistic's fiber is generally singular with respect to ambient Lebesgue measure. The ratio `f_X(x)/f_T(T(x))` and an ambient integral over a null fiber are not a general valid proof. Use disintegration/dominated statistical models, or state an explicitly discrete theorem. Visually verified. |
| L5 pp11–12, minimal sufficiency | Ratios must handle zero likelihoods/common null sets. A positive common-support version avoids zero denominators; it does not cover the uniform examples. |
| L5 pp14–15, Rao–Blackwell example | The factorial formula is valid only in its admissible range. Outside `1 <= t <= k(n-1)+1`, the probability of one success is zero. Use a binomial-coefficient formula with explicit boundary cases. |
| L6 p1, causal identification | Conditional unconfoundedness also needs overlap/positivity and consistency of observed and potential outcomes. |
| L6 pp3–4, MLE first-order condition | Differentiability alone does not imply a zero score at a constrained/boundary maximum. Require an interior local maximum. Log-likelihood comparison requires positive likelihood or an extended logarithm convention. |
| L6 p4, normal/uniform MLE | The normal variance MLE may fail to exist in the positive-variance parameter space if all observations coincide. The uniform endpoint MLE requires a positive observed maximum when the parameter space is positive. |
| L6 p4, uniform likelihood indicators | The density initially includes the endpoints, but the later likelihood uses strict indicators `theta > X_(n)` and `X_(1) > 0`. The strict upper inequality excludes the claimed maximizer `theta = X_(n)`; with that version the supremum is not attained. Use the original closed-support density to obtain the stated endpoint MLE. Visually verified during the semantic audit. |
| L6 pp4–5, information equalities | State sufficient local domination conditions for differentiating the density integral twice. A bound only on the second log-density derivative, as written, does not justify all interchanges automatically. |
| L6 p7, Cramér–Rao | Require finite, positive Fisher information and explicit differentiation-under-integral regularity. |
| L6 p8, uniform counterexample | Outside regular models information need not add: the joint uniform score is `-n/theta`, so its squared expectation is `n^2/theta^2`, not `n/theta^2`. The displayed latter value is only the invalid regular-model calculation. |

These qualifications are not additional axioms. Any theorem claiming a result
must prove it from its stated hypotheses. Restricted results must be labeled as
restricted results, and must not be counted as the general theorem.

## Gaussian passages checked against rendered pages

The normal-sampling theorem and proof on L2 pp7–8, the quadratic-form passage
on L1 p15, and the variance-estimator comparison on L5 p4 were checked visually
against the preserved PDFs in addition to the extracted text.

* `NormalSamplingDistribution` uses the centered standardized observations
  `(X_i - mu) / sqrt(v)`, where `v` is the population variance. Projection
  removes the common mean. The chi-square degrees of freedom are `n - 1`,
  and the t-statistic denominator is `sqrt(s^2 / n)`.
* `normal_sampleVariance_pos` proves that the sample variance is positive
  almost surely for `n > 1` and `v > 0`. The t and F ratios therefore have
  nonzero random denominators outside null sets.
* `NormalFStatistic` retains the population-variance ratio in the denominator;
  it permits different means and variances in the two samples.
* `GaussianMahalanobis` uses positive definite covariance, the nondegenerate
  covariance condition in the source, and proves cancellation of its matrix
  square root with its inverse.
* `NormalVarianceRisk` uses `v^2` for the source's `sigma^4`, because `v`
  denotes variance. The two MSEs are `2*v^2/(n-1)` and
  `(2*n-1)*v^2/n^2`. Strict comparison requires `n > 1` and `v > 0`.

## Sufficiency and the parameter-independent estimator

L5 Definition 1 (p7) defines sufficiency by a conditional distribution that
does not depend on the parameter. `IsSufficientStatistic` in `RaoBlackwell.lean`
formalizes this as a measurable statistic and
one Markov kernel that agrees with the regular conditional law of the data
under every probability measure in the model. The sample space is nonempty
and standard Borel, as is the finite-dimensional Euclidean sample space in
the notes. Each parameter may have its own exceptional null set.

For L5 Theorem 5 (pp13–14), `raoBlackwellEstimator K U` integrates `U` against
that common kernel and has no parameter argument. The formal theorem places
existence of the measurable estimator before the universal parameter
quantifier. It derives the conditional-expectation identity, square
integrability, mean preservation, MSE reduction, and the unbiased variance
comparison. `sufficientKernel_of_disintegration` gives a measure-level
criterion for the common conditional law. The general density factorization
and minimal-sufficiency theorems remain separate unfinished work.

## Follow-up semantic audit

[SEMANTIC_AUDIT.md](SEMANTIC_AUDIT.md) records the review of every included
module, corrections to project definitions, and a concrete Bernoulli model
checking the strengthened exponential-family and regular-density definitions.
L5 p10 and L6 pp4 and 6 were additionally checked against rendered PDF pages.
