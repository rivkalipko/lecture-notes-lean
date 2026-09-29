# Audit of the September 29 export (Lectures 7–13)

Lectures 1–6 in the new export are byte-for-byte identical to the existing
sources. Lectures 7–13 are new. All thirteen PDFs are preserved unchanged.
This document records mathematical corrections; it is not a claim that every
source result has been proved. See the coverage ledger for proof status.

## Lecture 7: MLE theory

* The three assumptions printed in Theorem 1 (identification, common support,
  and an interior true parameter) do **not** suffice for MLE consistency.
  Existence and measurable selection of maximizers also need attention.
  The formal argmax theorem uses uniform convergence of the criterion and
  separation of the population maximum outside every neighborhood. A measurable
  error envelope avoids an unmeasurable supremum. It proves convergence, rather
  than assuming consistency as an extra hypothesis.
* Different density values at a single point do not identify distributions:
  densities are defined up to null sets. Identification must distinguish laws.
* Asymptotic normality needs consistent interior score roots, a score CLT,
  convergence of curvature near the truth, and positive finite information.
  A pointwise LLN at the true parameter does not justify evaluation at a random
  intermediate parameter. The limit argument is separated from these analytic
  obligations. In higher dimensions information must be nonsingular.
* Logistic log-likelihood concavity does not establish existence or uniqueness
  of a finite maximizer: separation and deficient design rank matter.
* A variable constrained to be nonpositive cannot have a **nondegenerate**
  centered Gaussian limit. For the uniform endpoint MLE, the square-root
  normalization instead converges to zero; the faster rate is relevant.
* Pseudo-likelihood/KL comparisons require the appropriate absolute continuity
  and integrability. Information equality need not hold under misspecification.

## Lectures 8–9: tests and optimality

* The notes call their **acceptance** set `C` the critical region. The Lean API
  instead explicitly names the rejection set and uses measurable rejection
  probabilities in `[0,1]` for randomized tests.
* A level bound means rejection probability **at most** α throughout the null.
  Exact size is a separate assertion; a supremum need not be attained.
* A valid p-value is superuniform under every null distribution. It is not a
  posterior probability that the null is true. Bonferroni needs no independence.
* The two-sided Gaussian sample-size calculation discards the far-tail term.
  The resulting formula is not an exact inversion of the two-sided power
  function. Positive variance and a nonzero effect are required.
* Two-sided absolute-value bars can disappear in text extraction. The source
  images must be checked before interpreting a displayed acceptance inequality.
* The Neyman–Pearson necessity condition holds **almost everywhere**, not at
  every sample point. The source divides by a threshold allowed to be zero;
  the formal equality-case proof treats zero without that division.
* Theorem 2's assertion of **strictly** decreasing power does not follow from
  non-strict MLR. Identical distributions for different parameter values give
  a counterexample. The valid conclusion is nonincreasing power.
* Calibration is necessary: an exact deterministic size may not be available
  in a discrete model, and randomization at ties may be needed. The MLR proof
  explicitly assumes a calibrated cutoff, positive densities on common support,
  and a cutoff in the statistic's image. It does not prove general cutoff
  existence from the source's incomplete statement.
* Likelihood suprema require nonempty domains and boundedness/attainment for
  finite real arithmetic. Ratio bounds require a positive full-model supremum.
* Bootstrap validity is a conditional triangular-array claim, not an immediate
  application of the original-sample CLT. Empirical variance with divisor n
  differs from unbiased sample variance. Empirical quantile indexing needs a
  specified convention and valid indices. Edgeworth refinements need more than
  the informal conditions stated in the notes.

## Lecture 10: LR, Wald, and score

* The scalar Wilks proof requires actual likelihood expansion, consistent
  curvature, and a nondegenerate asymptotically normal MLE. The formal limit
  argument states these inputs explicitly rather than calling unspecified
  regularity sufficient.
* Irredundant constraints do not imply a full-rank constraint Jacobian. For
  example `g(θ)=θ²` at zero is a single irredundant constraint with zero derivative.
  The usual χ² degrees-of-freedom result requires a regular constraint manifold.
  Equal parameter and constraint counts do not guarantee a singleton null.
* Positive definite limiting covariance is required for ordinary inverse-based
  Wald statistics and their claimed degrees of freedom.
* `LM ≤ LR ≤ W` is not a universal ordering for every hypothesis in every
  normal model. Such finite-sample comparisons need the particular model and
  hypothesis specified. Reparameterization can change Wald statistics.
* The Poisson example has `W=20`, `LM=100/6`, and
  `LR=200*(5*log(5/6)+1)`. A χ² approximation does not give exact finite-sample size.

## Lecture 11: confidence sets

* Test inversion preserves the inequality: tests of level at most α give
  coverage at least `1−α`, and the reverse construction gives a level bound,
  not necessarily exact size α.
* Pratt's length identity is Tonelli's theorem for the measurable confidence
  graph. Nonnegative extended integrals permit infinite expected length.
  The optimality assertion assumes a UMP test for **each** singleton null.
  Removing the true singleton from the parameter integral requires it to have
  zero reference measure, as it does for Lebesgue length.
* Example 3 incorrectly calls the usual two-sided Student test UMP over all
  level-α tests. This does not follow from the earlier one-sided UMP theorem;
  therefore its unrestricted shortest-expected-length conclusion is not
  justified. Unbiasedness/invariance restrictions are a different claim.
* Studentization requires positive asymptotic variance. A delta-method
  transformation with zero derivative does not justify the displayed division.
* Visual review confirms that the Bernoulli score confidence set on page 5 has
  absolute-value bars; omitting them would incorrectly retain only one tail.
* Pointwise asymptotic coverage and uniform coverage are different assertions.
  Projection gives conservative simultaneous coverage. Two marginal 95%
  intervals need not have joint coverage **strictly** below 95% in degenerate
  perfectly dependent cases; equality can occur.

## Lecture 12: Bayesian updating

* Updating requires positive finite evidence. General posterior kernels are
  conditional distributions specified only almost everywhere under the prior
  predictive law.
* A prior-null **set** stays posterior-null. Zero mass at the single true point
  under a continuous prior does **not** imply inconsistency: every point has
  zero mass, while posterior mass in neighborhoods may converge to one.
* Gamma parameters in the notes are shape and **scale**. The posterior scale
  is `β/(n*β+1)`, not the posterior rate.
* The exponential-family conjugate-kernel recipe still needs a finite positive
  normalizing constant; arbitrary hyperparameters need not define proper priors.
* A minimum-volume HPD statement needs a reference measure, existence of a
  suitable density cutoff, and appropriate treatment of ties. HPD sets need
  not be connected intervals. They are not invariant under nonlinear changes
  of parameter.
* Theorem 1 does not specify regularity conditions, a metric for normal
  approximation, or a sampling mode of convergence of the random posterior.
  General Bernstein–von Mises is substantially stronger than pointwise Taylor
  expansion of a likelihood, and is not proved merely by defining a Gaussian
  approximation or assuming that the posterior already converges.
  `PosteriorAsymptotics` now proves a scalar theorem under explicit local
  quadraticity and integrable domination, including exact coordinate changes,
  uniform event error, and an almost-sure sampling version. These sufficient
  hypotheses are stronger than the usual weak informal regularity claim.
  `NormalPosteriorLimit` verifies them for a quadratic normal-mean likelihood
  with a bounded continuous integrable prior positive at the true parameter.
* Posterior-odds testing with a cutoff of one presupposes symmetric losses.

## Lecture 13: decision theory and shrinkage

* General loss is nonnegative. Extended-real risks prevent divergent real
  integrals from being silently assigned zero. Real finite-risk calculations
  explicitly impose moment conditions.
* A pointwise posterior-risk minimizer is a Bayes rule provided it is measurable
  and exists. The formal theorem permits a prior-predictive null exceptional set.
* The general sentence “Bayes estimators are admissible” requires qualification.
  The finite-parameter proof is valid for finite risks and strictly positive
  weight at every parameter. Priors that ignore some parameters do not give
  that conclusion without further hypotheses.
* James–Stein's strict risk improvement needs positive sampling variance and
  dimension at least three. Its correction is singular at zero. Integration
  by parts for globally smooth functions alone does not justify its use: the
  singularity and inverse-square integrability must be handled.
* Pointwise oracle shrinkage is not one estimator: its coefficient depends on
  the unknown parameter. The minimax claim needs a lower bound as well as an
  estimator attaining it. Domination of a minimax rule transfers minimaxity,
  but does not by itself establish the initial minimax lower bound.

## Source integrity

SHA-256 values for the added PDFs:

| PDF | SHA-256 |
| --- | --- |
| Lecture7_Notes.pdf | `51960756f046e35b5b90ad0e26e9fbb24ae039b8d7e2a43183f1b47a336586a0` |
| Lecture8_Notes.pdf | `28482eee2f70eb3fa6e2a6ffa682e8b44a007c5225f4a5e656b57bae1fe38c44` |
| Lecture9_Notes.pdf | `c140307afcd358a642898df9e14929ca1184fec9bb71af1165fcbbb7415bbf6d` |
| Lecture10_Notes.pdf | `76200dacd77b50eadeea1be8aabdea444871c773ba2ab9137715b946fff2ecd3` |
| Lecture11_Notes.pdf | `9846821c01b4d81276dac802e56bbb51ba035fdfb2bfe407d188271b84f58394` |
| Lecture12_Notes.pdf | `52b18f555de3d162858477f4f456f8df097cd24360c87f7a2d8ce130e4fe83d2` |
| Lecture13_Notes.pdf | `153e8df9319b57a88770a385e5488c6d60d98db0c4981807b38feb9fbc6f9cc4` |
