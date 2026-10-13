# Wave 1b return

Compiled partial checkpoint on local branch `chile-epistemic-evolution`.
The count-law keystone is complete; all of Part A is not complete.

## What compiled

`CountProfileCombinatorics`, `IIDCountLaw`, `PluralityCountFormula`, and
`PluralityCountExamples` compile together in `lake build SEKernel.EpistemicFinite`.

- Actual IID count-vector multinomial/factorial law, binary binomial law, and
  conditional uniform shuffle, including a zero-mass unconditional bridge.
- Actual first-active-label counting and fixed-count first-coordinate j/N.
- Full actual multinomial plurality formula with first-appearance tie weights.
- Actual five-draw consensus and false-consensus polynomial.
- All three actual Trap/mode probability witnesses: 992/3125,
  650997/1600000, and 5147/25000, evaluated through proved count formulas.

Headline names, hypotheses and source-result mappings:
[statement ledger](STATEMENTS_EPISTEMIC_WAVE1B.md),
[count-law details](EpistemicReports/Wave1b/COUNT_LAW.md),
[count-consumer details](EpistemicReports/Wave1b/COUNT_CONSUMERS.md).

## What remains unformalized

The overlapping 10/5 joint law and prefix-conditional weights; binary even/odd
accuracy identity; actual hump/prefix-realizability adapters; general-k derivatives;
weak-mode quantitative monotonicity; the specialized ten-voter union bound;
the two nonmodal and size-interaction examples; distribution-level variety; and
full collapsed-word/HLP/concentration transport. Existing Wave 1 algebra retains
its stated scope. The ledger gives the missing object for each result.

No delivered final source fails compilation. Omitted results have no admitted
stub or silently weakened substitute.

## Final axiom audit

All **52 new named theorems** are audited, including every headline theorem:
**51** use `[propext, Classical.choice, Quot.sound]`; `sum_boolCountProfile` uses
`[propext, Quot.sound]`. No other axiom occurs.

[Exact #print axioms output for all 52](EpistemicReports/Wave1b/AXIOMS.txt) ·
[names and counts](EpistemicReports/Wave1b/THEOREMS.json) ·
[hash-tied summary](EpistemicReports/Wave1b/AUDIT_SUMMARY.json).

The combined audit through Wave 2 covers **383** theorems: 380 standard trio,
2 `[propext, Quot.sound]`, and 1 with no axioms. No sorryAx, ofReduceBool or
trustCompiler appears. The comment-stripped forbidden-construct scan is clean.

## Build and custody

The final cold project build passed (exit 0, 7904 jobs).

The combined named umbrella build and audit exited 0; their
[receipts](EpistemicReports/ThroughWave2/VERIFICATION.json),
[build output](EpistemicReports/ThroughWave2/BUILD.log), and
[combined exact audit](EpistemicReports/ThroughWave2/AXIOMS.txt) are saved.
The [cold project build receipt](EpistemicReports/ThroughWave2/COLD_BUILD_RECEIPT.json)
records a build begun with the root project's `.lake/build` absent, retaining
pinned dependency caches fetched with `lake exe cache get`.

The original 19 protected files and six original Wave 1 mathematics sources are
byte-identical to their recorded bases. Nothing pushed, no PR, no remote changes,
no new commits. Wave 3 has not started.
