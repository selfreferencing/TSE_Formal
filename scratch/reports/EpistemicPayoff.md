# EpistemicPayoff wave-1 repair report

Date: 2026-10-12.
Source: `SEKernel/EpistemicPayoff.lean`.
Final compile: `lake build SEKernel.EpistemicPayoff`, exit 0; expanded actual-response receipt in `scratch/logs/EpistemicPayoff_realized_build_02.log` (7,892 jobs).

## Repairs

The existing root-authored theorem statements were preserved. Repairs added explicit classical decidability to event-based definitions, enumerated the three constructors of `Cell` with a proved finite-universe equality, beta-reduced pointwise event terms before proving nonnegativity, split iff proofs into their two directions, and supplied explicit multiples of the cell-weight normalization identity to algebraic proofs. No statement defect was found.

## What compiled

- The finite response-kernel and three-cell fixed-parameter definitions.
- The exact premium identity, lower/upper bounds, positivity criterion, and the corrected ceiling with explicit `absent ≤ post` hypothesis.
- Weighted transfer error, uniform transfer error, and the coarse identity.
- Finite arbitrary-partition accounting with explicit null-cell defaults.
- The two equivalent ten-call hump polynomial forms, endpoints, positivity, and reach-minus-vote polynomial identity.
- General-denominator imperfect-recognizer thresholds, the two-call instance, and the exact small-hump peak bound.
- Advocate aggregate ceilings, both nomination identities, coupled-stratum accounting, break-even algebra, four-decider polynomial, and finite numerical counterexamples.

## Remaining specification coverage

The current module does not claim the following results, which remain not formalized here:

- The strengthened prefix-realizability restriction: a prefix-only kernel with keep rate 1 cannot have post rate below 1. Obstacle: this needs an actual ordered-word extension/support argument, beyond the abstract cell model.
- General-k derivative identities and the fair-tie equality connecting even and odd binary voter counts. Obstacle: the binomial derivative/telescoping proof and ordered-word tie transport have not been installed.
- A theorem identifying the actual ordered-sampling institutional premium with `hump10`; only the exact polynomial identity is proved here.
- The distribution-level variety counterexample of Doc A A8.
- The random-posted-position chance-level example with p=1/4 and premium 3/32.
- Opposite-premium response-kernel existence witnesses on one comparison law.
- The specialized ten-draw union-bound conclusion `1 - V ≤ 10*(1-p)` and its fixed-cell corollary.

These omissions are explicit; no replacement axiom or hidden hypothesis was introduced.

## Actual-response integration

The final source now imports `FirstAppearancePlurality` and proves the missing
base accounting bridge. `CellModel.ofLaw` is an actual finite pushforward through
a partition; `comparatorModel` derives its cells from actual vote/reach events.
`correctness_bounds` proves that every genuine finite response kernel supplies
statewise probabilities in [0,1]. `conditionalRate_bounds` and
`responseRates_bounds` prove that conditional cell rates are in [0,1] when the
explicit null-cell default is in [0,1].

`response_conditional_cell_identity` proves the actual-law conditional-cell
identity. `response_premium_eq` identifies its derived cell premium with
`E(correctness) - P(vote)`, and `response_premium_identity` gives the three-cell
premium formula for that operational quantity. `response_premium_bounds` proves
the operational bounds with the explicit default-range premise.
`ordered_response_premium_eq` specializes the bridge to the actual IID ordered
word law, total plurality's `correctVote` predicate, and actual prefix reach.
No multinomial probability or unproved exchangeability input is used.

These additions close the base response-law integration gap; they do not close
prefix realizability, hump-sampling identification, derivatives, or majorization.

## Axiom audit

Command: `lake env lean /tmp/TSE_EpistemicPayoff_Realized_Audit.lean`, exit 0.
All 42 theorem declarations in the final expanded source returned exactly
`[propext, Classical.choice, Quot.sound]`.

```text
'SEKernel.EpistemicPayoff.correctness_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.cellOf_keep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.sum_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.CellModel.weight_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_le_post_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_transfer_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_transfer_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_transfer_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.premium_coarse_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.responseMass_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.conditionalRate_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.mass_mul_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.partition_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.CellModel.ofLaw_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.responseRates_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.comparatorModel_keep' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.response_conditional_cell_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.response_accuracy_eq_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.response_premium_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.response_premium_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.response_premium_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.ordered_response_premium_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.hump_forms_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.hump_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.hump_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.hump_reach_vote_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.mixed_recognizer_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.mixed_recognizer_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.recognizer_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.small_hump_peak' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.advocate_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.advocate_rescue_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.nomination_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.nomination_same_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.coupled_nomination_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.advocate_break_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.four_decider_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.correlated_uptake_differs' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.EpistemicPayoff.absent_rescue_ceiling_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
