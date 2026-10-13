# Bounded independent review: NoisySelection / PairedScores

Reviewed 2026-10-12 by the count-law worker, independently of the author of these two modules. Read-only source review; no Lean source was edited.

**Result: no material correctness or scope issue found in the reviewed modules or their lane report.**

## Evidence and scope

Read the complete `SEKernel/NoisySelection.lean` (1025 lines), complete `SEKernel/PairedScores.lean` (514 lines), and `scratch/reports/Wave2_NoisySelection.md`. Compared the paired sign/error, pooled-selection, Price, true-top variance, noisy recovery, and signal/noise statements with Doc A/B Part B and all of `PROOFCHECK_B.md`. Doc A had also been read in full during the earlier source gate.

An independent named-module build completed successfully:

```text
lake build SEKernel.NoisySelection SEKernel.PairedScores
Build completed successfully (7892 jobs).
```

Receipt: `scratch/logs/read_doc_a_review_noisy_build.log`. The author's separate final build and 88-theorem axiom audit remain their own receipts; this review did not rerun that axiom audit.

## Material checks

- The actual sorting implementation retains slot identity and sorts by descending score, then ascending integer key, then original index. Its `Survivors` output has exactly S distinct slots. `lexSurvivors_topSet` connects that algorithm to the structural top-set property.
- `pooled_count_ahead` and `pooled_count_behind` prove the strict-order genotype counts for that actual algorithm. `implemented_topS_master` consumes those facts, so the implemented master is not merely an expectation formula imposed as a premise. Tied conditional survivor count remains an explicit input, as the referee requires.
- `price_count_identity` uses expected genotype survivor counts and permits zero counts. It does not invoke the positive-weight proportional-selection result.
- `iid_win_sign` is proved on the actual finite product law and requires positive board count for strictness. The sign-reflection proof handles zero label masses.
- The sharper error proof compares actual loss/tie word masses with their symmetric square-root masses, derives the factor one half through reflection, and then proves the rational-base weakening. It never divides by the minus-outcome mass and covers b=0 and the empty product.
- `true_top_variance_bound` uses the actual selected and unselected indices and feasible fractional weights. The exchange certificate is structural and is not a hypothesis equivalent to the desired mean inequality. The resulting coefficient and population/survivor hypotheses match Doc A B5.3a.
- The noisy variance bound uses actual estimator variances, explicit unbiasedness, positive epsilon, and a finite union bound. The recovery theorem accepts explicit per-pair misranking bounds and preserves the distinction between those hypotheses and a proved scoring-model tail estimate. The experiment-scale vacuity note is qualified to the stated experimental parameters.
- The balanced consumer explicitly requires even population, 0<S<P, and fair tied count S/2. The incumbent correction is separate and agrees with the binding referee formula.
- The finite location-noise identity includes half-weight ties and endpoint atoms. Its mass-preserving reflection is an explicit structural input.
- Exact paired-score counterexamples are evaluated through the proved two-board outcome formula. The lane report correctly limits the top-S numeric evaluations to algebraic master-expression instances pending concrete stochastic realizations.

## Accepted coverage boundaries

The report expressly leaves actual uniform-slot/genotype tied-count identities, concrete roster/score/key realizations of the master numerics, the entire simulator transition, count-state non-Markov witness, several source count/coupling polynomials, and transmission-recursion compositions unformalized. This review does not promote those omissions to completed specification results. No material source-label overclaim was found after applying those stated boundaries.
