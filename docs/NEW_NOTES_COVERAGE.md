# Coverage of Lectures 7–13

This is an **incomplete** formalization. All included proof declarations are
checked by Lean, but that does not establish full coverage. “Partial” and
“restricted” below are not proofs of the unrestricted source statements.
No unproved theorem is exported as an assumption or disguised as a definition
of “regularity.” Source corrections are in [NEW_NOTES_AUDIT.md](NEW_NOTES_AUDIT.md).

## All nine numbered theorems

| Source | Status | What is actually established |
| --- | --- | --- |
| L7 T1, MLE consistency | **Corrected argmax theorem** | [MLEConsistency](../LectureNotes/MLEConsistency.lean): `argmax_consistency` proves convergence in probability from uniform criterion convergence, a well-separated population maximum, and maximization. `mle_maximizes_average_log` connects a positive likelihood MLE to the criterion. The source's three printed assumptions are insufficient; a uniform LLN and separation are not proved for every parametric density family. |
| L7 T2, asymptotic normality | **Partial: probabilistic reduction** | [AsymptoticTests](../LectureNotes/AsymptoticTests.lean): `score_root_limit` proves the Slutsky step from a normalized score limit, curvature convergence, and an almost-everywhere score expansion with nonzero curvature. Derivation of these hypotheses from an IID regular likelihood remains missing; this is not a full general MLE normality theorem. |
| L9 T1, Neyman–Pearson | **Proved for integrable dominated densities and randomized tests** | [NeymanPearson](../LectureNotes/NeymanPearson.lean): `StatisticalTest.neyman_pearson` and `neyman_pearson_necessity`. The necessity statement is almost everywhere, and the proof handles a zero threshold. `densityPower_eq_power` connects the weighted integral to the model measure, and `density_model_isProbabilityMeasure` proves normalization. Existence/calibration of a threshold is not asserted by these comparison theorems. |
| L9 T2, MLR UMP tests | **Restricted** | [MonotoneLikelihoodRatio](../LectureNotes/MonotoneLikelihoodRatio.lean): `mlr_lower_tail_threshold`, `mlr_lower_tail_power_antitone`, and `mlr_lower_tail_ump` prove composite-null optimality for a calibrated lower-tail rule. Densities are strictly positive, the parameter is ordered, and the cutoff is represented by a data point. General cutoff existence is not proved. The source's strict-monotonicity claim is corrected to nonincreasing power. |
| L10 T1, Wilks | **Partial: probabilistic reduction** | AsymptoticTests: `wilks_from_quadratic_expansion` proves the chi-square limit from the standardized MLE limit, normalized curvature consistency, and the actual quadratic expansion. Deriving the expansion and local curvature convergence for general regular likelihoods, and the constrained multivariate theorem, remains missing. |
| L11 T1, Pratt | **Proved** | [ConfidenceSets](../LectureNotes/ConfidenceSets.lean): `pratt_identity` is Tonelli for a jointly measurable confidence graph, permitting infinite expected length. `pratt_ump_confidence_minimal` proves optimal expected volume assuming a UMP test for each singleton null, with a reference measure having null singletons. The claimed two-sided Student-test application is not asserted. |
| L12 T1, posterior normal approximation | **Missing** | General Bernstein–von Mises, a sampling convergence mode for the random posterior, and asymptotic credible/frequentist agreement are not proved. Exact normal conjugacy in `NormalConjugacy` is not a replacement for this theorem. |
| L13 T1, posterior-risk minimization | **Proved for measurable minimizers** | [BayesianDecision](../LectureNotes/BayesianDecision.lean): `bayes_risk_eq_expected_posterior_risk` uses the actual posterior Markov kernel and prior predictive distribution; `posterior_minimizer_is_bayes` proves optimality, allowing an exceptional predictive-null set and infinite nonnegative risk. It does not assume existence of a measurable selector for arbitrary action spaces. |
| L13 T2, James–Stein | **Missing** | [NormalMeansDecision](../LectureNotes/NormalMeansDecision.lean) defines the ordinary and positive-part rules and proves measurability/origin behavior of the ordinary rule. It proves constant-shrinkage risks and oracle optimization. The singular Stein integration-by-parts argument, inverse-square integrability, strict data-dependent risk improvement, and minimax lower bound are not proved. |

## Definitions, proofs, and examples

| Material | Included | Remaining |
| --- | --- | --- |
| L7 MLE and logistic example | Uniform-error argmax bound and consistency; likelihood-to-log-criterion comparison. [LogisticRegression](../LectureNotes/LogisticRegression.lean): logistic probabilities strictly in `(0,1)`, normalized Bernoulli masses, actual log-likelihood identity, score derivative, second derivative, and nonpositive Hessian quadratic forms. | Exponential-model MLE law and information; logistic multivariate derivative identification and existence/uniqueness conditions; plug-in information estimates; sandwich covariance; bootstrap variance; nonregular and incidental-parameter examples. |
| L8 testing | [Testing](../LectureNotes/Testing.lean): measurable randomized tests, integral power, type-II error, level, UMP and unbiasedness, valid p-values, p-value threshold tests, Bonferroni with arbitrary allocations and no independence. | Full numerical Gaussian/chi-square power and quantile calculations, exact sample-size inversion, two-sample and bootstrap test-validity proofs. |
| L9 optimality and LRT | Neyman–Pearson integral comparison and equality case; MLR cross-product definition; composite-null lower-tail UMP result; derivative of unbiased power at a simple null. [LikelihoodRatio](../LectureNotes/LikelihoodRatio.lean): supremum-ratio definition, equality under attained maximizers, bounds, log-ratio identity. | General randomized-threshold existence, two-sided nonexistence/UMPU proofs, full Gaussian LRT example and ROC/Lagrangian applications. |
| L10 asymptotic tests | Standard-normal square has χ²(1) law; normal studentization; weak-limit rejection probabilities for null boundaries; equivalence of quadratic statistics from vanishing curvature differences. Scalar Wald/score formulas, Poisson score-statistic algebra, exact example values `W=20` and `LM=100/6`. | General model regularity, constrained vector LR/score limits, estimated-matrix inverse convergence, empirical balance/pre-trend applications, and numerical p-values. |
| L11 confidence sets | Coverage and level; exact test/coverage duality; projection coverage with measurable events; pointwise and uniform asymptotic coverage distinguished and uniform implies pointwise; Pratt identity/optimality; location and variance pivot inversion; Bernoulli score quadratic inequality. | Quantile-calibrated normal/variance intervals, Wilson endpoint formula, bootstrap quantile validity, ellipse projection endpoints, and applied examples. |
| L12 updating | [BayesianUpdating](../LectureNotes/BayesianUpdating.lean): evidence, normalized likelihood update, posterior integral formula, absolute continuity and preservation of prior-null sets, cancellation of parameter-independent factors. Normal posterior precision formulas and completing the square; Gamma shape/scale and posterior-mean algebra. [NormalConjugacy](../LectureNotes/NormalConjugacy.lean): normalized Gaussian density/kernel and exact Gaussian law of the normalized product of normal likelihood/prior kernels. | Full Beta/Gamma density conjugacy and moment calculations, general exponential-family conjugate normalization, MCMC, HPD optimal-volume theorem, and general posterior asymptotics. |
| L12 credible sets | Posterior Markov kernel, measurable credible-set definition, and posterior averaged over the predictive law equals the prior. | Exact quantile/HPD interval construction and posterior-odds decision rules for specified losses. |
| L13 decision theory | [DecisionTheory](../LectureNotes/DecisionTheory.lean): nonnegative extended-real risk and integrated risk; dominance, admissibility, Bayes rules, minimax and worst risk; transitivity/irreflexivity of dominance; finite-risk finite-parameter Bayes admissibility with strictly positive weights; inheritance of minimaxity under pointwise risk improvement; posterior-mean quadratic-loss optimality. Normal affine and vector constant-shrinkage risk and oracle coefficient optimality. | Constant-estimator admissibility in the full normal experiment; complete-class theorems; normal minimax lower bound; James–Stein dominance, positive-part improvement, and empirical-Bayes inverse-chi-square expectation. |

All new modules are imported in `LectureNotes.lean`. As with the original
lectures, proofs use established Mathlib results when appropriate; they are
not a line-by-line transcription of every informal argument in the PDFs.

## Verification

On 2026-09-29, the complete project passed `scripts/check.sh` with the pinned
Lean/Mathlib v4.33.0 dependencies: 45 imported source modules; successful build
(8752 jobs); and 754 audited declarations, including 605 theorem declarations
when private/compiler-generated declarations are counted. The new modules
contain 81 source theorem declarations and 44 source definitions/structures.
The source scan found no forbidden proof tokens and the dependency audit
found no forbidden logical assumptions. All thirteen PDFs match the supplied
export byte for byte. Local verification used a clean temporary checkout of
the same sources and pinned dependencies because macOS-offloaded files in the
original local toolchain were stalling reads.
