# Wave 2 return

Compiled partial checkpoint on local branch `chile-epistemic-evolution`.
This is a report of delivered finite results and explicit omissions, not closure
of every Part B specification result.

## What compiled

`MutationBaseline`, `NoisySelection`, `PairedScores`, and `ScorePooling` compile
together in `lake build SEKernel.EpistemicFinite`.

- Mutation transmission and mean recursion, fixed-point preservation, separate
  actual six-allele mutation law, and exact generations-1-to-7 mean
  `177168949182968/667572021484375`.
- Ordered full-state interface, actual lexicographic top-S sorting and three
  normalized tie-key laws; expected survivor counts and count-form Price identity;
  actual strict-outcome master adapter with explicit tied expected count.
- Corrected balanced formulas; structural true-top variance lower bound, oracle
  regret, finite noisy bounds and recovery. Noisy-bound docstrings record n<=36
  vacuity. Several numerical master instances are algebraic only.
- Actual IID paired-score sign theorem and sharp half-factor geometric error bound;
  moments, Cantelli consequences, actual numerical noise counterexamples, finite
  signal-to-noise identity and transmission/environment accounting.
- Actual fair-top-one unequal-evaluation probabilities; current/historical score
  comparisons; actual overlap strict-score probabilities, means and variances.

[Full statement ledger](STATEMENTS_EPISTEMIC_WAVE2.md) ·
[mutation/pooling names, hypotheses and omissions](EpistemicReports/Wave2/MUTATION_AND_POOLING.md) ·
[selection/paired-score mapping](EpistemicReports/Wave2/SELECTION_AND_PAIRED_SCORES.md).

## What remains unformalized

Actual conditional tied-count identities for the three implemented key laws;
the identical-outcome incumbent mutation floor and multi-generation comparison;
complete simulator transition and count-state non-Markov witness; several paired
tie/count polynomials and numerical witnesses; fixed-discordance coupling;
affine covariance/variance adapters; task-heterogeneity total variance; and
historical-pooling survival adapters and mixture examples.

Fair balanced sign carries an explicit fair tied expectation. Historical pooling
proves strict-score events and a defined share observable; its link to the actual
protected-incumbent sort is open. The 1/8 versus 1/12 and -47/30000 statements
are master-expression arithmetic, pending concrete stochastic realization.
Optional continuous analysis remains outside the umbrella.

No delivered final source fails compilation. Unfinished results are absent,
with reasons in the mappings; no admitted stub was installed.

## Final axiom audit

All **137 new named theorems** are audited, including every headline theorem.
Every one uses exactly `[propext, Classical.choice, Quot.sound]`.

[Exact #print axioms output for all 137](EpistemicReports/Wave2/AXIOMS.txt) ·
[all names](EpistemicReports/Wave2/THEOREMS.json) ·
[hash-tied summary](EpistemicReports/Wave2/AUDIT_SUMMARY.json).

The combined audit through Wave 2 covers **383** theorems: **380** standard trio,
**2** `[propext, Quot.sound]`, and **1** with no axioms. No sorryAx, ofReduceBool,
trustCompiler or other unexpected axiom appears. The comment-stripped source scan
finds no forbidden declarations or proof constructs.

## Build and custody

The final cold project build passed (exit 0, 7904 jobs).

Combined `lake build SEKernel.EpistemicFinite` and
`lake env lean SEKernel/AxiomsAuditEpistemic.lean` exited 0:
[command receipts](EpistemicReports/ThroughWave2/VERIFICATION.json),
[build log](EpistemicReports/ThroughWave2/BUILD.log),
[exact combined audit](EpistemicReports/ThroughWave2/AXIOMS.txt),
[verification/hash summary](EpistemicReports/ThroughWave2/AUDIT_SUMMARY.json).
The [cold project build receipt](EpistemicReports/ThroughWave2/COLD_BUILD_RECEIPT.json)
records the root-project rebuild with pinned dependency caches retained.
Non-fatal linter warnings remain.

All 19 original protected files and six original Wave 1 mathematics sources are
unchanged. HEAD is still bd80f4a; no new commits, pushes, PRs or remote changes.
Stopped before Wave 3.
