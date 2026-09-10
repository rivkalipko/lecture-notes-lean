# Lecture notes formalized in Lean

This repository contains a checked Lean 4 transcription of the reusable
definitions, algebraic identities, and theorem interfaces from the six MIT
14.380 lecture notes supplied with the project.  Every proof in the source
tree is compiled by Lean; there are no `sorry`, `admit`, or axiom placeholders.

The source PDFs are included unchanged.  `docs/SOURCE_AUDIT.md` records
hypothesis gaps and typographical issues found while transcribing them.  A
statement is only encoded after its hypotheses have been made explicit.  The
coverage ledger in `docs/COVERAGE.md` maps each lecture section to the Lean
declaration that represents it and identifies material that needs additional
measure-theoretic infrastructure.

The main modules are:

- `LectureNotes/Foundations.lean`: probability-space laws, conditional
  probability, expectation, variance, covariance, bias, and MSE.
- `LectureNotes/Sampling.lean`: sample-mean and centered-sum identities.
- `LectureNotes/Inequalities.lean`: Markov, Hölder, and squared-deviation
  Chebyshev inequalities using Mathlib's integrability hypotheses.
- `LectureNotes/Estimation.lean`: estimators, unbiasedness, factorization for
  exponential families, MSE decomposition, and shrinkage risk.
- `LectureNotes/LargeSample.lean`: convergence notions, Mathlib-backed SLLN and
  CLT interfaces, empirical CDF bounds, and bootstrap resampling.
- `LectureNotes/EstimationTheory.lean`: likelihood, log-likelihood, score,
  Fisher information, MLE, moment equations, and their elementary theorems.

## Build

With Lean 4 and `lake` installed:

```sh
lake build LectureNotes
```

The project pins Lean in `lean-toolchain` and pins the Mathlib revision in
`lakefile.toml`, so the build is reproducible once the dependencies are
downloaded.
