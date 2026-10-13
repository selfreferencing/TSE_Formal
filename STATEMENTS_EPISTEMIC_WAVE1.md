# Epistemic finite extension: statements and deviations

Prepared 2026-10-12 from the two supplied specifications, the Part A referee
files, the six Wave 1 source files, and the available worker build/audit reports.
This is the Wave 1 checkpoint ledger. Specifications contain mathematical proofs;
their word “proved” is not used as evidence of Lean formalization. The cold-build
and combined axiom-audit receipts are in RETURN_EPISTEMIC_WAVE1.md.

## Evidence and status convention

The source modules are `FiniteProbability`, `FirstAppearancePlurality`,
`FirstTiedLabelCounting`, `PluralityBounds`, `EpistemicPayoff`, and
`PluralityConcentration`, all under `SEKernel/`. The first-tie module is an
additional implementation module, rather than a replacement for the specified
multinomial probability results.

The integrated verification covers the exact sources delivered with this checkpoint.
See `EpistemicReports/Wave1/` for full build and axiom output.

- **Proved** means the stated Lean theorem proves the described result.
- **Proved under an explicit hypothesis** means the named theorem exposes the
  substantive restriction identified in the scope column.
- **Counterexample, algebra only** identifies an exact abstract arithmetic
  witness. It does not identify the underlying ordered stochastic experiment.
- **Not formalized** means no theorem proving that specification result was
  found. A nearby definition, general-purpose ingredient, or algebraic identity
  is listed as context without promoting the missing result.

Every exact law-based numerical counterexample requested in the handoff remains
**not formalized**. Two small algebraic witnesses in `EpistemicPayoff` are
explicitly distinguished below from probability-law counterexamples.

## Conventions and notation

1. `N` and prefix size `k` range over natural numbers including zero. Probability
   formulas for a prefix explicitly assume `k ≤ N`. Results needing positive
   sample size carry `0 < n`. This adopts Doc B's zero-inclusive convention.
2. `SEKernel.Epistemic.OrderedWord N A` is `Fin N → Option A`; `none` is
   abstention. The plurality rule returns `none` exactly on an all-abstention
   word, including length zero.
3. `SEKernel.Epistemic.voteAccuracy π N correct` is the probability called
   `V_N` in the specifications. `correctVote` is the event, and `plurality` is
   the deterministic selector. These are separate objects.
4. Abstention mass is `π.mass none`; correct mass is `π.mass (some correct)`.
   No globally overloaded `u` is introduced. The formalization does not silently
   identify abstention mass with a mutation parameter or an uptake parameter.
5. The two-count bound uses parameters `higher`, `lower` and
   `countTailCoefficient higher lower = (higher-lower)^2/(2*(higher+lower))`.
   Sample size is `N`. Correct-mode bounds carry explicit positivity of correct
   mass and explicit strict modal gaps.
6. The number of wrong labels in common modal bounds is
   `Fintype.card {a : A // a ≠ correct}`. The first-tie denominator is the
   cardinality of active original positions, not the number of answer labels.
7. `EpistemicPayoff.Cell` uses constructors `keep`, `post`, `absent`;
   `Epistemic.ComparatorCell` uses `keep`, `posted`, `absent`. These are two
   distinct finite types. `CellModel.ofLaw` and `comparatorModel` explicitly
   derive the payoff cells from an actual experiment; `ordered_response_premium_eq`
   connects them to the ordered vote and prefix-reach predicates. This does not
   assert that arbitrary fixed response triples are prefix-realizable.
8. The abstract payoff parameter function is `κ : Cell → ℝ`; calibration is
   `κhat`. In `mixedRecognizer` the parameter is `uptake`. `response` is used in
   the smaller hump and simple recognizer statements. The ten-draw polynomial
   is `hump10`; its factored form is `hump10Factored`.
9. The concentration coupling uses word length `s`, probabilities `θ`, `η`,
   integer threshold `ℓ`, and reward `g`. Its three symbols are `Fin 3`.

## Finite probability and experiment objects

| Specification result | Lean name(s) | Status and exact scope |
|---|---|---|
| Doc A F0 definitions; Doc B A1.1 finite laws and expectation | `SEKernel.FiniteProbability.Law`, `SEKernel.FiniteProbability.Law.prob`, `SEKernel.FiniteProbability.Law.expect`, `SEKernel.FiniteProbability.Law.variance`, `SEKernel.FiniteProbability.Law.covariance` | Proved definitions and finite algebra. `expect` and `variance` are definitionally the existing `SEKernel.Law1.mean` and `SEKernel.Law1.variance`. |
| Product experiments and finite stochastic kernels | `SEKernel.FiniteProbability.Law.prod`, `SEKernel.FiniteProbability.Law.pi`, `SEKernel.FiniteProbability.Law.bind`, `SEKernel.FiniteProbability.Law.map`, `SEKernel.FiniteProbability.Kernel`, `SEKernel.FiniteProbability.Kernel.comp`, `SEKernel.FiniteProbability.Kernel.comp_mass` | Proved normalization by finite sums/products. Dependent coordinate types are allowed in `Law.pi`; no side-branch dependency. |
| Doc A F0 (0.1), finite total expectation | `SEKernel.FiniteProbability.Law.total_expectation`, `SEKernel.FiniteProbability.Law.prob_mul_conditionalMean`; `SEKernel.EpistemicPayoff.partition_expectation`, `SEKernel.EpistemicPayoff.mass_mul_conditional` | Proved for an explicit finite classification map. The probability module uses zero on null cells; the payoff module allows arbitrary supplied null-cell defaults. Mass-weighted accounting is independent of the default. |
| Finite Markov inequality | `SEKernel.FiniteProbability.Law.markov`, `SEKernel.FiniteProbability.Law.markov_mul`, `SEKernel.FiniteProbability.Law.prob_le_expect` | Proved under explicit nonnegativity of the observable and positivity of the threshold. |
| Doc A F0 (0.2), Chebyshev | `SEKernel.FiniteProbability.Law.chebyshev` | Proved for every finite law and positive deviation threshold, using the actual variance. |
| Doc B finite Cantelli ingredient, later used in B2.5 | `SEKernel.FiniteProbability.Law.cantelli`, `SEKernel.FiniteProbability.Law.shifted_square` | Proved for every finite law and positive one-sided threshold, including zero variance. The paired-score specialization is Wave 2. |
| Doc A F0 (0.3), iid empirical mean and variance | `SEKernel.FiniteProbability.Law.iid_average` | Proved under `0 < n`; the random variables are functions of distinct coordinates of an explicit iid product law. |
| Doc A F0 nonidentical independent variance sum | `SEKernel.FiniteProbability.Law.variance_pi_sum`, `SEKernel.FiniteProbability.Law.expect_pi_coord_mul`, `SEKernel.FiniteProbability.Law.expect_pi_prod` | Proved for functions of separate actual product coordinates. `variance_pi_sum` uses a common coordinate sample type; the product and product-moment constructors permit heterogeneous dependent types. |
| Finite independence referee fix | `SEKernel.FiniteProbability.Law.expect_pi_coord_mul`, `SEKernel.FiniteProbability.Law.variance_pi_sum`, `SEKernel.FiniteProbability.Law.iid_average`; `SEKernel.Epistemic.prob_pi_forall` | Proved constructive product-coordinate formulation, rather than an unspecified predicate called independent. |
| Finite union bounds | `SEKernel.FiniteProbability.Law.prob_union_le`, `SEKernel.FiniteProbability.Law.prob_exists_le` | Proved. Specialized ten-call failures are not automatically counted as installed corollaries. |
| Doc A optional input H; Doc B optional Hoeffding/limits | — | Not formalized in Wave 1; intentionally excluded from the finite umbrella. No external concentration theorem is installed as an axiom. |
| Doc B A1.1 task-fitness aggregation | — | Not formalized as a separately named theorem/definition beyond finite expectation. The generic mean infrastructure is available. |

## Ordered plurality, count laws, reach, and consensus

| Specification result | Lean name(s) | Status and exact scope |
|---|---|---|
| Doc A A1; Doc B A1.2 total ordered first-appearance plurality | `SEKernel.Epistemic.OrderedWord`, `SEKernel.Epistemic.labelCount`, `SEKernel.Epistemic.candidatePositions`, `SEKernel.Epistemic.plurality`, `SEKernel.Epistemic.plurality_eq_none_iff`, `SEKernel.Epistemic.plurality_empty` | Proved total selector. It chooses the least actual position among readable positive maximal-count positions. |
| Mandatory relabelling lemma | `SEKernel.Epistemic.labelCount_relabel`, `SEKernel.Epistemic.candidatePositions_relabel`, `SEKernel.Epistemic.plurality_relabel` | Proved for an actual equivalence of option alphabets fixing abstention. The selected position is preserved. |
| Winner occurrence, maximality, and first appearance | `SEKernel.Epistemic.plurality_mem_word`, `SEKernel.Epistemic.plurality_maximal_count`, `SEKernel.Epistemic.plurality_dominates_readable`, `SEKernel.Epistemic.plurality_first_maximal` | Proved on actual ordered words. |
| Doc A A1/Doc B A1.3 three comparator cells | `SEKernel.Epistemic.reaches`, `SEKernel.Epistemic.correctVote`, `SEKernel.Epistemic.comparatorCell`, `SEKernel.Epistemic.comparatorCell_keep_iff`, `SEKernel.Epistemic.comparatorCell_posted_iff`, `SEKernel.Epistemic.comparatorCell_absent_iff`, `SEKernel.Epistemic.cellProbability_total`, `SEKernel.Epistemic.cellProbability_keep` | Proved deterministic cells and normalization of their actual finite-law probabilities. |
| Referee correction: V need not imply prefix R | `SEKernel.Epistemic.correctVote_need_not_reach_prefix` | Proved concrete length-two word `(none, correct)` with prefix length one. The stronger false universal negation was not installed. |
| Correct vote implies full-word reach | `SEKernel.Epistemic.correctVote_reaches_full`, `SEKernel.Epistemic.voteAccuracy_le_reach_full` | Proved. These do not assert prefix reach. |
| Doc B A3.1 iid ordered sample law and V₀=0 | `SEKernel.Epistemic.iidWordLaw`, `SEKernel.Epistemic.voteAccuracy`, `SEKernel.Epistemic.voteAccuracy_zero` | Proved product law and empty-word accuracy. |
| Missing first-tied-label counting step, genuine arrangement law | `SEKernel.Epistemic.uniformLaw`, `SEKernel.Epistemic.firstActive_uniform`, `SEKernel.Epistemic.firstActive_label_probability`, `SEKernel.Epistemic.firstTLabel_probability`, `SEKernel.Epistemic.firstTLabel_semantics`, `SEKernel.Epistemic.shuffledWord_labelCount` | Proved on the uniform law on permutations of original positions of a fixed word. Active positions are nonempty and the target label lies in T. The first T-labelled entry has probability `u_a/L`; actual least-index semantics and count preservation are proved. |
| Conditional-iid-to-uniform-arrangement bridge | — | Not formalized. No theorem identifies an iid law conditioned on its count vector with the shuffle pushforward of `uniformLaw (Perm (Fin N))`. No exchangeability premise was substituted for this missing proof. |
| Doc B A3.1 unconditional multinomial plurality formula | — | Not formalized. Distinct fixed-count word fibers have not been enumerated by `N!/∏c_a!`, and the previous conditional-law bridge is missing. Defining the ordered law does not prove the count formula. |
| Doc A A4.1; Doc B A4.1 reach probability | `SEKernel.Epistemic.no_appearance_probability`, `SEKernel.Epistemic.reach_full_probability`, `SEKernel.Epistemic.reach_prefix_probability` | Proved on the actual iid word law: `1-(1-p)^k`, with `k ≤ N`; includes zero prefix and zero word length. |
| Doc A A4.2; Doc B A4.1 exact overlap accounting | `SEKernel.Epistemic.jointVote_partition`, `SEKernel.Epistemic.cellProbability_posted`, `SEKernel.Epistemic.cellProbability_absent` | Proved actual-event identities `V=vR+vU`, posted=`reach-vR`, absent=`1-reach-vU`. No independence between vote and reach is assumed. |
| Doc B A4.1 displayed max/min posted-cell bounds | — | Not separately formalized as named max/min bounds. Exact event identities and generic probability monotonicity are proved ingredients. |
| Doc A A4.3–A4.4; Doc B A4.2 exact two-block multinomial joint law | — | Not formalized. The prefix/suffix count weights and conditional first-tie weights have not been transported to the iid ordered law. The actual-event accounting above is a different, weaker result. |
| Doc A A5.1 fair binary ties; referee probability `j/n` | — | Not formalized on the iid law conditioned on correct count. `firstActive_uniform` proves the relevant position symmetry for the shuffle law only; `V_(2k)=V_(2k-1)` is not installed. |
| Doc A A7 consensus; Doc B A7.1 consensus cells | `SEKernel.Epistemic.consensusAt`, `SEKernel.Epistemic.consensus_unique`, `SEKernel.Epistemic.consensusCell`, four `SEKernel.Epistemic.consensusCell_*_iff` theorems, `SEKernel.Epistemic.consensusCellProbability_total` | Proved actual deterministic strict-majority consensus with explicit `N < 2*threshold`; four cells include no consensus. |
| Actual consensus on the posted prefix of a longer full word | `SEKernel.Epistemic.postedWord`, `SEKernel.Epistemic.postedWord_reaches_full`, `SEKernel.Epistemic.postedWord_labelCount`, `SEKernel.Epistemic.prefixConsensusCell`, `SEKernel.Epistemic.prefix_consensus_unique`, four `SEKernel.Epistemic.prefixConsensusCell_*_iff` theorems, `SEKernel.Epistemic.prefixConsensusCellProbability_total`, `SEKernel.Epistemic.prefix_falseConsensus_probability_cells` | Proved on the actual first k positions, with `k ≤ N` and strict-majority condition `k < 2*threshold` where needed. The ambient probability law remains the full ordered-word law. This supplies the intended five-posted consensus cells when N=10,k=5,threshold=3 without counting the unposted suffix as part of the trigger. |
| Doc B A4.4 disjoint false-consensus partition | `SEKernel.Epistemic.falseConsensus_probability_cells`, `SEKernel.Epistemic.falseConsensus_probability_eq_sum` | Proved probability identity: wrong-consensus mass equals the disjoint sum of wrong-label threshold-event probabilities. |
| Doc B A4.4 five-draw polynomial `Σ(10q³−15q⁴+6q⁵)` | — | Not formalized. The threshold-event probabilities have not been identified with the binomial polynomial on the actual iid word law. |
| Zero-mass labels are inert on the current alphabet | `SEKernel.Epistemic.zero_mass_reach`, `SEKernel.Epistemic.zero_mass_voteAccuracy`; `SEKernel.EpistemicConcentration.zero_label_word_mass`, `SEKernel.EpistemicConcentration.zero_label_event_restriction` | Proved: appearance/winning have zero probability; every event has unchanged mass after restricting to words avoiding the zero-mass label. |
| Invariance under adjoining/deleting zero-mass labels by alphabet embedding | — | Not formalized as a full cross-alphabet pushforward adapter. The current-alphabet zero-mass event restriction is not that adapter. |

## Modal probability bounds

| Specification result | Lean name(s) | Status and exact scope |
|---|---|---|
| Doc B A3.2 two-readable-count geometric tail | `SEKernel.Epistemic.iid_count_geometric_bound`, `SEKernel.Epistemic.countTilt_product`, `SEKernel.Epistemic.expect_countTilt`, `SEKernel.Epistemic.rational_tilt_moment` | Proved on the actual iid word law for distinct readable labels and an explicit strict mass gap. Coefficient is exactly `(h-l)^2/(2*(h+l))`; no Hoeffding input. |
| Doc B A3.2 rational tail | `SEKernel.Epistemic.iid_count_rational_bound`, `SEKernel.Epistemic.geometric_le_rational`, `SEKernel.Epistemic.countTailCoefficient_bounds` | Proved `(1-a)^N ≤ 1/(1+Na)`, including `N=0`; coefficient positivity and upper bound are proved from the law. |
| Doc B A3.3 strict correct mode, labelwise bounds | `SEKernel.Epistemic.correct_mode_geometric_bound`, `SEKernel.Epistemic.correct_mode_rational_bound`, `SEKernel.Epistemic.failed_vote_count_witness` | Proved under explicit `p>0`, all strict wrong-label gaps, and existence of a wrong readable label. All-abstention words are covered by the count-witness union. |
| Doc B A3.3 common coefficient and finite cutoff | `SEKernel.Epistemic.correct_mode_common_rational_bound`, `SEKernel.Epistemic.correct_mode_cutoff` | Proved under an explicitly supplied positive common coefficient lower bound and its per-label inequalities. No implicit minimum or inverse of zero mass is used. An exact integer-ceiling construction is not installed. |
| Doc B A3.3 one-readable-label case | `SEKernel.Epistemic.sole_readable_accuracy` | Proved exact equality with reach under `Subsingleton A`. No convergence is claimed without positive correct mass. |
| Doc B A3.3 wrong larger mode | `SEKernel.Epistemic.wrong_mode_geometric_bound`, `SEKernel.Epistemic.wrong_mode_rational_bound`, `SEKernel.Epistemic.readable_winner_dominates` | Proved on actual iid words under an explicit wrong-label probability greater than correct probability. The displayed wrong-mode sample cutoff is not separately installed. |
| Doc A A3.1–A3.3 second-moment probability bounds | — | Not formalized in their stated `p+q−δ²`, `1/N`, and inverse-gap forms. General finite Chebyshev and iid variance are proved, and Doc B's geometric bounds are proved; a stronger bound is not recorded as a proof of the exact Doc A formula without its comparison argument. |
| Doc A A3.4 optional exponentials; all modal limits | — | Not formalized; intentionally deferred to optional analysis. |
| Doc B optional tie-at-the-mode completion | — | Not formalized: no named `V_N=(1/h)P(winner∈H)` or tied-mode finite remainder theorem. Deterministic relabelling alone is not recorded as the probability symmetry theorem. |
| Doc B A3.4 weak-mode voter monotonicity | — | Not formalized. The artificial relabelling prior, Bayes-value comparison, and `u^N(1-u)/M` increment lower bound have not been constructed in Lean. |
| Doc A A3.5; Doc B A3.5 nonmodal counterexamples | — | Not formalized as ordered probability laws; exact fractions are listed in the numerical ledger below. |
| Doc A A3.6; Doc B after A4.4 operational Trap versus mode | — | Not formalized as law-based examples; the false-consensus polynomial identification is absent. |

## Payoff, hump, recognition, and advocacy

| Specification result | Lean name(s) | Status and exact scope |
|---|---|---|
| Doc A A1; Doc B A1.3 response kernels | `SEKernel.EpistemicPayoff.ResponseKernel`, `SEKernel.EpistemicPayoff.correctness`, `SEKernel.EpistemicPayoff.correctness_bounds` | Defined as a finite output law at each complete state, including abstention; correctness is proved to lie in `[0,1]` from row normalization. No prefix-realizability theorem is implied. |
| Actual cell-model constructor | `SEKernel.EpistemicPayoff.CellModel.ofLaw`, `SEKernel.EpistemicPayoff.comparatorModel`, `SEKernel.EpistemicPayoff.comparatorModel_keep` | Proved normalized pushforward of an actual finite law through a partition map; the comparator keep mass is exactly `P(vote)`. |
| Actual conditional cell rates and null-cell range | `SEKernel.EpistemicPayoff.responseRates`, `SEKernel.EpistemicPayoff.conditionalRate_bounds`, `SEKernel.EpistemicPayoff.responseRates_bounds` | Proved conditional correctness rates of the actual response kernel; rate bounds require the explicit default to lie in `[0,1]` on every cell. Weighted identities permit arbitrary null-cell defaults because their contribution is zero. |
| Doc A A2.1; Doc B A2.1 premium accounting | `SEKernel.EpistemicPayoff.CellModel.ofLaw_accuracy`, `SEKernel.EpistemicPayoff.response_conditional_cell_identity`, `SEKernel.EpistemicPayoff.response_accuracy_eq_expect`, `SEKernel.EpistemicPayoff.response_premium_eq`, `SEKernel.EpistemicPayoff.response_premium_identity` | Proved for an actual finite experiment law, arbitrary vote/reach events, and an actual finite response kernel. The law-derived premium is exactly `E(correctness)-P(vote)` and equals the conditional three-cell expression. No independence or prefix-realizability premise is smuggled into the identity. |
| Ordered-word instantiation of premium accounting | `SEKernel.EpistemicPayoff.ordered_response_premium_eq` | Proved on `iidWordLaw π N` with the actual total `correctVote` and actual prefix `reaches` predicates: operational response accuracy minus `voteAccuracy π N right` equals the law-derived cell premium. No multinomial formula is used. |
| Abstract fixed-parameter premium algebra | `SEKernel.EpistemicPayoff.CellModel`, `SEKernel.EpistemicPayoff.CellModel.accuracy`, `SEKernel.EpistemicPayoff.CellModel.premium`, `SEKernel.EpistemicPayoff.premium_identity` | Proved independently of the actual-kernel instantiation. Arbitrary normalized weights and parameter triples remain a separate modeling object; there is no claim that every triple is realized by a prefix-only institution. |
| Doc A A2.2–A2.3; Doc B A2.1 bounds and sign | `SEKernel.EpistemicPayoff.premium_bounds`, `SEKernel.EpistemicPayoff.premium_pos_iff` | Proved under the explicit cell-rate range where needed. |
| Actual response premium bounds | `SEKernel.EpistemicPayoff.response_premium_bounds` | Proved for the actual response kernel, actual `P(vote)`, and actual conditional keep rate, with the explicit default-range premise. |
| Doc A A2.4; Doc B A2.4 transfer | `SEKernel.EpistemicPayoff.premium_transfer_identity`, `SEKernel.EpistemicPayoff.premium_transfer_bound`, `SEKernel.EpistemicPayoff.premium_transfer_uniform` | Proved weighted error `Σp_c|κ_c−κhat_c|` and a supplied uniform ε bound. The maximum-over-cells corollary and nested task-weight calibration bound are not separately named. |
| Corrected `D ≤ κ_post` ceiling after Doc B A4.3 | `SEKernel.EpistemicPayoff.premium_le_post_rate` | Proved under explicit `κ_absent ≤ κ_post` and rates in `[0,1]`. The word “universal” is not used. |
| Doc A A2 opposite signs; Doc B A2.2 response-kernel existence | — | Not formalized as two actual finite response kernels on one comparison law. |
| Doc A A2 chance-pickup example; Doc B A2.3 | — | Not formalized as an ordered-law counterexample. No proved count formula connects the claimed `5/32` vote probability to the finite experiment. |
| Doc A A4.5–A4.7; Doc B A4.3 wrong-mode reach/premium remainders | — | Not formalized as named finite cell bounds, `−2e_N` remainder, or `(1-p)^k+2(1-a)^N` premium error. Ordered-event identities, modal tails, and fixed-cell algebra are available ingredients. Limits are deferred. |
| Doc A A5.1 at k=5; Doc B A5.1 polynomial equivalence | `SEKernel.EpistemicPayoff.hump10`, `SEKernel.EpistemicPayoff.hump10Factored`, `SEKernel.EpistemicPayoff.hump_forms_equal`, `SEKernel.EpistemicPayoff.hump_reach_vote_polynomial`, `SEKernel.EpistemicPayoff.binaryVote9`, `SEKernel.EpistemicPayoff.reachPolynomial` | Proved algebra for arbitrary real p. The expanded and factored polynomial forms are equal; hump10 equals the named reach polynomial minus the named nine-vote polynomial. |
| Ten-call hump endpoints and interior sign | `SEKernel.EpistemicPayoff.hump_endpoints`, `SEKernel.EpistemicPayoff.hump_positive` | Proved as polynomial facts; interior positivity assumes `0<p<1`. |
| Doc B A5.1 `hump10 = p_Post = actual ideal-recognizer premium` | — | Not formalized. The actual 10/5 sampling identification and finite enumeration of binary position sets are missing. Algebraic names `binaryVote9` and `reachPolynomial` do not supply the probability bridge. |
| Doc A A5.1 general-k hump | — | Not formalized. No general-k binomial coefficient polynomial identity or actual-sampling identification is installed. |
| Doc A A5.2 general-k derivative identities; referee gap 5 | — | Not formalized. Both the binomial-tail derivative identity and the combinatorial coefficient identity required to derive `D_*'` are missing. |
| Doc A A5.2 peak `126^(−1/4)` and general root; Doc B after A5.3 interior-maximum existence/derivative characterization | — | Not formalized; these belong in optional analysis and are absent from the finite umbrella. |
| Doc B A5.1 simple r-recognizer threshold | `SEKernel.EpistemicPayoff.recognizer_threshold` | Proved algebra `0 < response*reach-vote ↔ vote/reach < response`, under `reach>0`. It does not construct the actual prefix response law or identify its masses. |
| Doc A A5.3 imperfect recognizer | `SEKernel.EpistemicPayoff.mixedRecognizer`, `SEKernel.EpistemicPayoff.mixed_recognizer_threshold`, `SEKernel.EpistemicPayoff.mixed_recognizer_two` | Proved algebra with explicit positive mixed-post denominator. The two-call polynomial factorization is proved. Identification of `mixedRecognizer` with an actual posted-only response kernel and identification of `vote` with `V_(2k)` are not installed. |
| Strengthened prefix-only compatibility obstruction | — | Not formalized. In the specified binary 10/5 law, the required statement is that keep rate 1 forces post rate 1, excluding every post rate below 1. No weakened restriction or equivalent hypothesis has been substituted. |
| Doc B A5.1 union bounds and A5.2 endpoint/retention/invention corollaries | — | Not formalized as sampling statements, including `1-V ≤ 10*(1-p)` and the corrected abstract-cell formulation of (A5.6). Generic union and premium bounds are proved but not the specialized conclusions. |
| Doc B A5.3 smaller-design peak | `SEKernel.EpistemicPayoff.small_hump_peak` | Proved algebraic bound `3*r*p*(1-p)^2 ≤ 4*r/9` and equality iff `p=1/3`, under `0≤p≤1`, `r>0`. The actual N=k=3 sampling identification is not formalized. |
| Doc A A7.1; Doc B A7.2 gain accounting | `SEKernel.EpistemicPayoff.advocateGain`, `SEKernel.EpistemicPayoff.coupled_nomination_identity` | Proved supplied-stratum finite-sum algebra. The generic partition theorem is also available. A separately named instantiation of the actual four consensus cells and off-trigger fallback is not installed. |
| Doc B A7.2 general advocate ceiling | `SEKernel.EpistemicPayoff.advocate_ceiling` | Proved for supplied nonnegative cell masses and changed rates at most one. |
| Doc B A7.2 stronger aggregate rescue ceiling | `SEKernel.EpistemicPayoff.advocate_rescue_ceiling` | Proved with explicit nonpositive aggregate outside-rescue contribution. This is the specified stronger hypothesis formulation, rather than requiring loss in each outside cell. |
| Doc A A7.1 / Doc B A7.3 unqualified rescue-ceiling counterexample | `SEKernel.EpistemicPayoff.absent_rescue_ceiling_counterexample` | Counterexample, algebra only: the supplied three-cell gain is exactly 1 when all mass is assigned absent and the response rate changes 0→1. A complete response-kernel/consensus-word construction is not formalized. |
| Doc A A7.2; Doc B A7.4 both nomination identities | `SEKernel.EpistemicPayoff.nomination_identity`, `SEKernel.EpistemicPayoff.nomination_same_baseline`, `SEKernel.EpistemicPayoff.coupled_nomination_identity` | Proved finite algebra, including the extra-pathway term and the no-other-pathway specialization. No causal interpretation is attached. Actual conditional-law parameter identification is not separately installed. |
| Doc B A7.5 four-decider following polynomial | `SEKernel.EpistemicPayoff.four_decider_polynomial` | Proved polynomial equality only. Conditional iid binary response probability and its fair 2–2 tie count are not formalized. |
| Doc B A7.5 marginal-following nonidentification witness | `SEKernel.EpistemicPayoff.correlated_uptake_differs` | Counterexample, algebra only: at f=1/4, f differs from `3f²−2f³`. No actual perfectly correlated four-answer law or probability identification is formalized. |
| Doc A A7.3; Doc B A7.6 break-even share | `SEKernel.EpistemicPayoff.advocate_break_even` | Proved algebra under explicit positive trigger probability and positive gain-plus-cost denominator. The trigger/cell expectation equation is not separately instantiated. |
| Causal interpretation of nomination | — | Not a T1 theorem. Observational accounting supplies no causal identification, consistent with both specifications. |
| Doc A A8 distribution-level variety counterexample; Doc B A8.1 state-level witness | — | Not formalized as probability/response-law counterexamples. |
| Doc A A8 coarse identity; Doc B A8.2 / (A8.1) | `SEKernel.EpistemicPayoff.premium_coarse_identity` | Proved exact algebra under the CellModel normalization field. |
| Doc B A8.2 / (A8.2) reach-mass transfer ε(κ_post−κ_none) | — | Not separately formalized as a named theorem on changed normalized cell models. |

## Concentration and majorization

| Specification result | Lean name(s) | Status and exact scope |
|---|---|---|
| Doc B A6.1 explicit L/M/H reflection | `SEKernel.EpistemicConcentration.reflect`, `SEKernel.EpistemicConcentration.reflect_involutive`, `SEKernel.EpistemicConcentration.symbolCount_reflect`, `SEKernel.EpistemicConcentration.wordMass_reflect_ge`, `SEKernel.EpistemicConcentration.reflect_loss_iff_gain`, `SEKernel.EpistemicConcentration.central_word_mass_balancing` | Proved on literal words `Fin s → Fin 3`. The loss/gain transport uses `Finset.sum_bij`; nonnegative word-mass comparison is proved from `0≤θ≤η≤1/2`. |
| Doc B A6.1 central probability comparison | `SEKernel.EpistemicConcentration.balancingLaw`, `SEKernel.EpistemicConcentration.central_probability_balancing` | Proved on the normalized explicit product coupling: compare counts #L and #L+#M on the same words. A separate theorem rewriting these probabilities as binomial-coefficient sums is not installed. |
| Doc B A6.1 finite layer cake and symmetric reward conclusion | `SEKernel.EpistemicConcentration.symmetric_layer_cake`, `SEKernel.EpistemicConcentration.symmetric_word_mass_balancing`, `SEKernel.EpistemicConcentration.symmetric_expectation_balancing` | Proved exact finite layer cake and expectation order, with explicit reward symmetry and monotonicity up to the center. This is the specified probability content on actual coupling coordinates. |
| Doc A A6 count-weight identity (A6.1) | — | Not formalized: the `1/m`, `d_m/m`, `(1-d_m)/m` conditional count weights and their monotonicity are absent. |
| Doc B A6.2 collapsed-word factorization and one balancing transfer | — | Not formalized. No finite collapsed-word pushforward/fiber factorization connects the balancing coupling to the actual ordered plurality winner or both overlapping cells. |
| Doc B A6.3 HLP sorted-list induction | — | Not formalized. No HLP transfer characterization or finite transfer chain theorem is installed, and it is not assumed as a premise. |
| Doc A A6 theorem; Doc B A6.4 fixed-size concentration/premium | — | Not formalized. The current results stop at the balancing coupling; voting/cell monotonicity and the premium theorem have not been transported through collapsed words and HLP. |
| Fixed-constant versus one-fixed-kernel qualification | — | Binding statement restriction for future work: any premium theorem must take fixed parameter constants `κ∈[0,1]^3`. The assertion using conditional means of one fixed response kernel is false; no such theorem was installed. |
| Doc A size-interaction counterexample; Doc B A6.5 | — | Not formalized as ordered probability-law counterexamples; both requested examples are listed below. |

## Exact numerical and concrete counterexample ledger

All entries in this table are **not formalized as the stated law-based or
ordered-state counterexample**, even where a polynomial substitution could be
evaluated arithmetically. No fraction here is represented as a Lean-checked
probability without its count-law bridge.

| Source | Required witness/calculation | Remaining obstacle |
|---|---|---|
| Doc A A2; Doc B A2.3 | p=1/4, three-voter accuracy 5/32, random-posted accuracy 1/4, premium 3/32 | Actual random-position response law and plurality count probability. |
| Doc A A3.5 | `(2/5,1/2,1/10)` with accuracies `2/5,49/125,2/5` at N=2,3,4 | Multinomial/count formula on actual first-appearance words. |
| Doc B A3.5 | `(3/8,1/8,1/2)` with accuracies `3/8,93/256,189/512` at N=2,3,4 | Same probability bridge. |
| Doc A A3.6 | Correct strict mode `(11/20,9/20)` but wrong consensus `650997/1600000 > 3/10` | Five-draw consensus polynomial identification. |
| Doc A A3.6 converse | Correct mass 1/5, wrong masses 3/10 and five copies of 1/10; wrong strict mode but wrong consensus `5147/25000 < 3/10` | Same consensus probability bridge. |
| Doc B after A4.4 | Correct strict mode `(3/5,2/5,0)` but wrong consensus `992/3125 > 3/10` | Same consensus probability bridge. |
| Doc B after A4.4 converse | `(correct,wrong,abstain)=(1/4,1/3,5/12)`; wrong mode but wrong consensus `17/81 < 3/10` | Same consensus probability bridge. |
| Doc A A6 size interaction | p=3/5, wrong masses `(2/5,0)` versus `(1/5,1/5)`; concentration premium differences `10962/78125` at N=8 and `54054/390625` at N=9, interaction `−756/390625` | Actual count formula and response-law premium identification. |
| Doc B A6.5 size interaction | p=3/4; concentrated premiums D₄=39/256, D₅=105/1024; diffuse D₄=51/512, D₅=285/4096; interaction `−81/4096` | Same count/premium bridge. |
| Doc A A8 distribution-level variety | p=1/3, N=k=3; distinct counts `5/3` versus `19/9`, vote `7/27` versus `1/3`, premium `4/9` versus `10/27` | Distinct-count expectation, actual plurality count law, and perfect-recognizer law. |
| Doc B A8.1 state-level variety | Prefix `(correct,w,w,w,w)` versus `(w,w,w,u,z)`, five w suffix; variety 2→3 and response premium r→0 | Concrete ordered-word plurality/count proofs and prefix response-kernel witness. |
| Doc A A7 discussion | Zero following with r=1, baseline 1/2 gives gain −1/2 | No separately named actual response-law counterexample. |

The already proved `correctVote_need_not_reach_prefix` is a concrete
deterministic word counterexample, rather than one of these numerical
probability-law examples. The two small advocate arithmetic witnesses are
described in the payoff table with their narrower scope.

## Binding fixes and final coverage boundary

- Separate-coordinate finite independence is installed.
- “V need not imply R” has an actual deterministic witness.
- The missing first-T formula is installed on a genuine fixed-word permutation
  law, with least-index semantics. Conditional iid uniformity and multinomial
  enumeration remain explicit gaps.
- The conditional `j/n` fair-binary-tie step and general-k derivative identities
  remain unproved in Lean.
- The payoff ceiling includes the required absent/post order hypothesis; the
  weighted transfer error is independent of null-cell conventions.
- The strengthened prefix obstruction remains unproved in Lean, including the
  endpoint case post rate 0. The abstract fixed-cell model is not presented as
  a realizable posted-only kernel.
- The ten-call union-bound specialization and corrected abstract (A5.6)
  statement are not installed.
- Probability bounds preserve strict mass gaps and correct-mass positivity.
- The ordered comparator, actual iid probability law, abstract cell parameters,
  polynomial algebra, and uniform-permutation arrangement law remain distinct
  named objects. An explicit adapter now identifies the law-derived response-cell
  premium with operational `E(correctness)-P(vote)`. It does not identify arbitrary
  cell constants with a prefix-only response kernel, or supply a multinomial or
  hump-sampling bridge.
- The concentration module proves a substantial finite coupling and layer-cake
  theorem. It does not prove the requested plurality majorization theorem.
- The wave is therefore a compiled **partial Wave 1**, with the integrated cold build and audit
  recorded in the Wave 1 return. Waves 2 and 3 and optional analysis are
  not covered by this mapping. No push, PR, remote change, or public acceptance
  is implied.

## Later-wave specification inventory

All following specification results are **not formalized: scheduled Wave 2 or
Wave 3, neither started at this checkpoint**. Their source mathematical status
is not a Lean status. Optional analysis is also not started. The stop after
Wave 1 is intentional. There are no placeholder Lean files or weakened theorem
statements for these results.

| Source | Specification result | Lean name | Status / reason |
|---|---|---|---|
| Doc B | B0.1: full finite transition normalization | — | Not formalized: later wave, not started. |
| Doc B | B1.1–B1.3: mutation baseline and exact finite mean | — | Not formalized: later wave, not started. |
| Doc B | B2.1: sign of randomized paired win probability | — | Not formalized: later wave, not started. |
| Doc B | B2.2: monotonicity at fixed discordance | — | Not formalized: later wave, not started. |
| Doc B | B2.3: gap alone orders win probabilities | — | Not formalized: later wave, not started. |
| Doc B | B2.4: finite rational score-error bound | — | Not formalized: later wave, not started. |
| Doc B | B2.5: finite Cantelli bound | — | Not formalized: later wave, not started. |
| Doc B | B2.5: Hoeffding score bound | — | Not formalized: optional analysis, not started. |
| Doc B | B2.6: equal average accuracy implies fair heterogeneous comparison | — | Not formalized: later wave, not started. |
| Doc B | B2.7: top-\(S\) expectation and transmission contrast | — | Not formalized: later wave, not started. |
| Doc B | B2.8: fair pairwise scores imply abundance neutrality | — | Not formalized: later wave, not started. |
| Doc B | B3.1: exact incumbent tie penalty | — | Not formalized: later wave, not started. |
| Doc B | B3.2: discreteness alone guarantees ties | — | Not formalized: later wave, not started. |
| Doc B | B3.3: complete incumbent suppression | — | Not formalized: later wave, not started. |
| Doc B | B3.4: neutral random ties restore the control baseline | — | Not formalized: later wave, not started. |
| Doc B | B4.1: greater variance, even symmetric unimodal, implies enrichment | — | Not formalized: later wave, not started. |
| Doc B | B4.2: wider-scale rare challenger wins upper-tail advantage | — | Not formalized: optional analysis, not started. |
| Doc B | B4.3: identical current outcomes give identical current scores | — | Not formalized: later wave, not started. |
| Doc B | B4.4: finite historical-pooling enrichment despite identical payoffs | — | Not formalized: later wave, not started. |
| Doc B | B5.1: covariance plus transmission plus environment identity | — | Not formalized: later wave, not started. |
| Doc B | B5.2: variance/SS-1-shaped gain | — | Not formalized: later wave, not started. |
| Doc B | B5.3: unbiased truncation always raises mean fitness | — | Not formalized: later wave, not started. |
| Doc B | B5.4: two-type sign under balanced blocks or a supplied monotone coupling | — | Not formalized: later wave, not started. |
| Doc B | B5.5: approximate true-top-set recovery | — | Not formalized: later wave, not started. |
| Doc B | B6.1: larger gap improves reliability in a fixed family | — | Not formalized: later wave, not started. |
| Doc B | B6.2: equal variance and larger mean force more wins | — | Not formalized: later wave, not started. |
| Doc B | C.1: advocate conditional replicator and silent neutrality | — | Not formalized: later wave, not started. |
| Doc B | C.2: exact finite solution and half-frequency ordering criterion | — | Not formalized: later wave, not started. |
| Doc B | Universal “board first” ordering | — | Not formalized: later wave, not started. |
| Doc B | C.3: crossover and linkage with both parent protocols | — | Not formalized: later wave, not started. |
| Doc B | C.4: mutation, elitism, and history-conditioned transitions | — | Not formalized: later wave, not started. |
| Doc B | Expected conditional frequency equals ratio of expected counts | — | Not formalized: later wave, not started. |
| Doc B | C.5: removing voters automatically suppresses the silent allele among voters | — | Not formalized: later wave, not started. |
| Doc B | Restricted silent-allele supply level \(1/15\) | — | Not formalized: later wave, not started. |
| Doc B | D.1: clone variance, effective size, lineage bound | — | Not formalized: later wave, not started. |
| Doc B | D.2: distribution estimation and wrong-mode finite bounds | — | Not formalized: later wave, not started. |
| Doc B | Answer distribution alone identifies the correct label | — | Not formalized: later wave, not started. |
| Doc B | Additional observations weakly improve optimal finite decision value | — | Not formalized: later wave, not started. |
| Doc B | D.3: partial-correlation effective size | — | Not formalized: later wave, not started. |
| Doc B | D.4: effective size determines majority accuracy | — | Not formalized: later wave, not started. |
| Doc B | E.1: reach-only marginal and finite spawning wedge | — | Not formalized: later wave, not started. |
| Doc B | E.2: general three-cell diminishing returns | — | Not formalized: later wave, not started. |
| Doc B | E.3: greedy allocation, threshold, and slot LP certificate | — | Not formalized: later wave, not started. |
| Doc B | E.4: automatic–deliberate optimal support and finite error | — | Not formalized: later wave, not started. |
| Doc B | E.4: complete-allocation Law2/KKT encoding | — | Not formalized: later wave, not started. |
| Doc B | E.5: forecast regret and biased-policy divergence | — | Not formalized: later wave, not started. |
| Doc B | E.5: selection transmits correction with no policy heredity | — | Not formalized: later wave, not started. |
| Doc B | E.6: absence and finite innovation arrival | — | Not formalized: later wave, not started. |
| Doc B | Modal/geometric limits and optional peak existence | — | Not formalized: optional analysis, not started. |
| Doc B | All reported F1–F15 numerical effects, intervals, correlations, ordering frequencies, and replay multipliers | — | Not formalized: empirical T3 evidence; no theorem constants. |
| Doc A | B1: mutation recursion, fixed point, and seven-generation mean | — | Not formalized: later wave, not started. |
| Doc A | B2: IID paired ranking sign and finite-power error bound | — | Not formalized: later wave, not started. |
| Doc A | Ranking reliability is ordered by Δ alone | — | Not formalized: later wave, not started. |
| Doc A | B2: shared-genotype top-S transition and composition threshold | — | Not formalized: later wave, not started. |
| Doc A | Fair pairwise ranking implies neutral top-S selection | — | Not formalized: later wave, not started. |
| Doc A | B3: exact tie probability and incumbent penalty | — | Not formalized: later wave, not started. |
| Doc A | Score lattice alone guarantees a tie | — | Not formalized: later wave, not started. |
| Doc A | B3: no-survival mutation floor and neutral group-tie baseline | — | Not formalized: later wave, not started. |
| Doc A | B4: variance alone, or symmetric unimodality alone, favors newcomers | — | Not formalized: later wave, not started. |
| Doc A | B4: independent fixed-scale newcomer theorem | — | Not formalized: optional analysis, not started. |
| Doc A | B4: historical-task composition and current-pool equality | — | Not formalized: later wave, not started. |
| Doc A | B5: Price covariance and quantitative propensity condition | — | Not formalized: later wave, not started. |
| Doc A | B5: oracle variance advantage, noisy regret, and finite variance tail | — | Not formalized: later wave, not started. |
| Doc A | B5: balanced-block and pairwise-tournament sign theorems | — | Not formalized: later wave, not started. |
| Doc A | Unbiased shared-genotype truncation always increases true mean fitness | — | Not formalized: later wave, not started. |
| Doc A | B5: evidence multipliers, transmission/feedback, control-contrast recursion | — | Not formalized: later wave, not started. |
| Doc A | B6: fixed finite-noise shift comparison, variance identities and bounds | — | Not formalized: later wave, not started. |
| Doc A | Larger mean with equal variance always improves rank reliability | — | Not formalized: later wave, not started. |
| Doc A | B6: Gaussian comparison | — | Not formalized: optional analysis, not started. |
| Doc A | B7: full finite replay and appearance probability | — | Not formalized: later wave, not started. |
| Doc A | C1: clonal conditional odds and finite convergence bounds | — | Not formalized: later wave, not started. |
| Doc A | C2: crossover, linkage, and actual two-locus transmission | — | Not formalized: later wave, not started. |
| Doc A | C3: exact board-before-advocate condition and finite hitting bounds | — | Not formalized: later wave, not started. |
| Doc A | Conditional expression forces board-first threshold ordering | — | Not formalized: later wave, not started. |
| Doc A | Removing voters lowers the silent allele among voters | — | Not formalized: later wave, not started. |
| Doc A | C4: deterministic mutation map, finite conditional-frequency sum, tie floor | — | Not formalized: later wave, not started. |
| Doc A | D1: clone effective count and equality case | — | Not formalized: later wave, not started. |
| Doc A | D2: partial-correlation effective count | — | Not formalized: later wave, not started. |
| Doc A | D3: IID distribution estimation and truth nonidentification | — | Not formalized: later wave, not started. |
| Doc A | E1: exact extra-proposer value and geometric marginal | — | Not formalized: later wave, not started. |
| Doc A | Generic three-cell diminishing returns | — | Not formalized: later wave, not started. |
| Doc A | E2: greedy allocation, price certificate, whole-allocation LP lift | — | Not formalized: later wave, not started. |
| Doc A | E3: automatic and deliberate optimal-set agreement | — | Not formalized: later wave, not started. |
| Doc A | E3: biased forecast divergence and nontransmission barrier | — | Not formalized: later wave, not started. |
| Doc A | All reported effect sizes, model-specific responses, historical incidence, and replay error factors | — | Not formalized: empirical T3 evidence; no theorem constants. |
