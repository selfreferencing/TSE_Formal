# Wave 2: mutation baseline and score pooling

Both new modules compile. `scratch/logs/ScorePooling_build_06.log` ends with `Build completed successfully (7892 jobs)`. A second worker read both complete sources and checked the report against Doc A/B Part B; its final check is described below. No Lean source repair was necessary.

## MutationBaseline (namespace `SEKernel.MutationBaseline`)

Build receipt: the MutationBaseline dependency build in `scratch/logs/ScorePooling_build_02.log` passed. All 23 theorems have `#print axioms` receipts in `scratch/logs/MutationBaseline_axioms.log`; each is exactly `[propext, Classical.choice, Quot.sound]`.

| Specification result | Lean theorem(s) | Scope/status |
|---|---|---|
| Doc A B1.1; Doc B B1.1 conditional affine transmission | `transmission_identity`, `offspring_mean`, `finite_population_transmission` | Proved. `offspringLaw` is an actual Bernoulli finite law. Population theorem sums arbitrary dependent offspring observables with the explicit marginal expectation hypothesis; it does not impose unneeded independence. |
| Uniform-survival specialization | `expect_affineStep`, `neutral_expectation` | Proved under explicit `L.expect Y = x`. Actual uniform-subset inclusion-probability combinatorics is not proved in this module. |
| Fixed point | `fixed_point` | Proved with `u+d ≠ 0`; fixed-point preservation, without uniqueness when replacement rate is zero. |
| Doc A B1.2; Doc B B1.2 exact neutral recursion | `meanTrajectory_closed`, `meanTrajectory_distance` | Proved for the recursion of means, generation index `t=0,1,…`; `u+d ≠ 0` explicit. |
| Finite-horizon mean | `geometric_sum_start_one`, `meanTrajectory_average` | Proved, averaging generations 1 through `T`; `T>0` and coefficient `≠1` explicit. |
| Finite coefficient bounds and monotone-from-zero expectation | `coefficient_bounds`, `meanTrajectory_zero_monotone` | Proved with parameter bounds and sign assumptions explicit. No sample-path monotonicity claim. |
| Doc B B1.3 six-allele mechanism | `sixAllele_voter_to_board`, `sixAllele_board_to_voter`, `sixAllele_fixed_point` | Proved for actual `sixAlleleMutation q hq hq' a : Law (Fin 6)`, voter allele 0, five board alleles; locus-hit rate `q` explicit. |
| Numerical coefficients and trajectory | `experiment_coefficients`, `experiment_trajectory` | Proved. |
| Exact mean generations 1 through 7 | `experiment_seven_generation_mean` | Proved: `177168949182968 / 667572021484375`; derived from the closed trajectory then `norm_num` over seven terms. |

No analytic convergence theorem is formalized; it belongs to the optional analytic module. Doc A's general `K,M` allele-count instantiation and explicit binary-flip instantiation are not formalized; the aggregate transition interface and requested six-allele law are formalized. The architecture-identification caveat is respected by keeping the six-allele instance separate from the interface theorem.

## ScorePooling (namespace `SEKernel.ScorePooling`)

All 26 named theorems have matching `#print axioms` receipts in `scratch/logs/ScorePooling_axioms.log`, each exactly `[propext, Classical.choice, Quot.sound]`. These are actual finite probability statements where a law is displayed, with the survivor-implementation boundary described explicitly below.

| Specification result | Lean theorem(s) | Scope/status |
|---|---|---|
| Doc A B4.3; Doc B B4.3 current weighted equality | `current_scores_equal` | Proved termwise finite weighted-score equality. The equality holds even without positivity or normalization of weights; no probabilistic or rank claim is inferred from it. |
| Doc A B4.3 historical composition examples | `historical_composition_examples` | Proved deterministic two-pool/one-pool examples in both directions. |
| Fair top-one slot ties | `topSlots_nonempty`, `fairTopLaw_count`, `fairTopLaw_three_zero` | Actual normalized top-one finite law, uniform over maximizing **slots**. Three-slot eligible-count formula is proved before numerical evaluation. This is not a theorem connecting this law to NoisySelection's permutation-key implementation. |
| Doc A B4.1 unequal Bernoulli evaluation witnesses | `unequal_evaluation_probability`, `unequal_evaluation_counterexamples` | Actual five independent Bernoulli coordinates, one newcomer evaluation and two per incumbent, followed by the actual fair-top-one law. Proved probability p-p^3+(p^5+(1-p)^5)/3 and exact values 71/240<1/3 and 19/48>1/3. The one-vs-two-score unbiasedness and variance comparison are not separately formalized, so the full variance-counterexample interpretation is not itself a single completed Lean theorem. |
| Doc B B4.4 overlap strict-score event | `historical_strict_win`, `past_all_true_probability`, `historical_survival_probability` | Actual shared-current-plus-independent-past law; incumbent has m+1 observations. Proved P(historical score < current score) = (1/2)(1-(1/2)^m), including m=0. Despite the theorem name, it formally states the strict-score event probability, not a selection-kernel survival probability. |
| Doc B B4.4 expected share and threshold | `historical_expected_share`, `historical_share_exceeds_current_iff` | Proved for the explicitly defined observable `newcomerSurvivorShare S`, which is the strict-win indicator divided by S. Positive P,S are explicit in the comparison iff. The link to an actual protected-incumbent top-S survivor law is not formalized; it additionally needs 1<=S<=P-1 and the one-newcomer roster/priority facts. |
| Doc B B4.4 numerical overlap witness | `historical_overlap_counterexample` | Actual strict-score event is 3/8 and the defined share observable has expectation 3/32>1/12. Concrete sort/retention realization remains unformalized. |
| Doc B B4.3/B4.4 identical current scores | `current_pool_strict_win_probability` | Proved self-comparison strict-win event has probability zero. The corresponding incumbent-selection survival-zero adapter is not formalized. |
| Doc B B4.4 unbiasedness and variances | `fairBit_mean`, `fairBit_variance`, `past_sum_mean`, `past_sum_variance`, `currentScore_mean`, `historicalScore_mean`, `currentScore_variance`, `historicalScore_variance` | Actual finite-law means are 1/2; variances are 1/4 and 1/(4(m+1)). Product coordinates preserve the shared-current overlap rather than assuming the two scores are independent. |

### Explicit omissions

- Doc A B4.1 symmetric-unimodal mixture witness 46/165 and Doc B B4.1 mixture witness 3217/12300 are not formalized. No unfinished scratch mixture is imported or promoted to a theorem.
- Doc A B4.3's general variance-of-difference/covariance identity and common-random-number sign qualification are not given new Lean theorems here.
- The continuous scale-family result and the referee's strict-CDF/countable-separated-points repair belong to the optional analysis module and are not formalized here.
- Uniform-survival inclusion combinatorics, the six-allele embedding into an entire five-locus genotype update, and full-score-kernel/retention composition are not formalized by these modules. The aggregate mutation interface and separate six-allele law are proved.

### Final review and receipts

The second-worker review read all 222 lines of MutationBaseline and all 336 lines of ScorePooling. No material mathematical correctness error or hidden conclusion-equivalent theorem premise was found. The stale pending-build wording above was repaired; no Lean source was edited. The historical-score/share-observable scope and the incomplete variance-interpretation component of the unequal-evaluation witness are now explicit.

The source theorem declarations exactly match the existing audit outputs: 23 MutationBaseline plus 26 ScorePooling, **49 total**, each with `[propext, Classical.choice, Quot.sound]`. The forbidden-token scan of both new sources is empty. Source SHA256, audit-output SHA256, and every theorem name are recorded in `scratch/chile/Wave2_MutationPooling_review_manifest.json`. The separate final named-module build receipt is `scratch/logs/read_doc_b_review_mutation_pooling_build.log`.

