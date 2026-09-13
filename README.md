# MIT 14.380 lecture notes in Lean

This is an **incomplete formalization** of the six supplied lecture notes.
The included results have Lean proofs, using Mathlib's measures, integrals,
conditional expectations, independence, and convergence of probability laws.
The project does not yet formalize every definition, theorem, example, or proof
in the PDFs.

The [coverage ledger](docs/COVERAGE.md) lists every numbered theorem and
distinguishes proved, restricted, and missing results. Major remaining work
includes Lindeberg–Feller, Glivenko–Cantelli and DKW, and sufficiency for general
dominated continuous models. A finite positive-support sufficiency theorem is
proved and is labeled with that restriction.

The [source audit](docs/SOURCE_AUDIT.md) records mathematical corrections and
extra hypotheses. The six source PDFs are preserved unchanged. Compilation
certifies the formal statements; it does not establish complete coverage or
literal agreement with an incorrect statement in the notes.

## Check the proofs

Install Lean using Elan, then run:

```sh
lake exe cache get
bash scripts/check.sh
```

Lean and Mathlib are pinned in `lean-toolchain` and `lake-manifest.json`.
The check script builds every source module and runs two audits:

* `scripts/check_sources.py` rejects placeholder tokens, unsafe proof shortcuts,
  and modules omitted from the root import file.
* `Audit.lean` follows the axiom dependencies of every project declaration,
  including private and compiler-generated declarations. It permits only
  `propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx`, project
  axioms, and any other axiom dependency.

GitHub Actions runs the same checks. A successful check means the **included
proofs** passed; it does not turn a missing coverage entry into a proved result.

## Organization

* Probability and moments: `Foundations`, `ProbabilityLaws`,
  `ConditionalExpectation`.
* Gaussian distributions: `GaussianQuadraticForms`, `GaussianMahalanobis`,
  `ChiSquaredMoments`.
* Sampling: `Sampling`, `SamplingMoments`, `NormalSampling`,
  `NormalSamplingDistribution`, `NormalFStatistic`, `NormalVarianceRisk`,
  `FinitePopulation`.
* Inequalities and limits: `Inequalities`, `Concentration`, `LargeSample`,
  `Convergence`, `WeakLaw`, `CramerWold`, `MultivariateCLT`, `DeltaMethod`,
  `StochasticOrder`.
* Empirical distributions: `EmpiricalDistribution`, `Bootstrap`.
* Estimation: `Estimation`, `Sufficiency`, `EstimationTheory`, `Information`,
  `RegularDensity`, `RegularCramerRao`.

Some proofs follow the notes' algebra or conditional-expectation argument;
others apply established Mathlib theorems, notably SLLN, scalar CLT, Jensen,
Hölder, Gaussian independence, and the subgaussian bound used for Hoeffding.
These are checked formal proofs, not line-by-line transcriptions of every
source proof.
