# Epistemic finite extension: current statement ledger

Current checkpoint: compiled partial Waves 1, 1b and 2. All 14 mathematics modules
build together through `SEKernel.EpistemicFinite`. Part A and Part B still contain
explicit omissions. Wave 3 and optional analysis have not started.

## Result maps and status precedence

1. [Wave 1b current Part A additions and remaining gaps](STATEMENTS_EPISTEMIC_WAVE1B.md).
2. [Wave 2 current Part B mappings and remaining gaps](STATEMENTS_EPISTEMIC_WAVE2.md).
3. [Historical Wave 1 full inventory and notation ledger](STATEMENTS_EPISTEMIC_WAVE1.md).

The first two addenda supersede the historical ledger only for their named
results. Other Wave 1 statuses and its Wave 3 inventory remain in force.
Historical “not formalized” and “not started” text is not current evidence for a
result explicitly closed by a later addendum. Specifications' written proofs
are never counted as Lean compilation.

“Proved” means the described theorem compiled; “proved under an explicit
hypothesis” exposes the substantive model restriction. “Counterexample, algebra
only” is distinguished from a probability statement on an actual finite law.
“Not formalized” means no delivered theorem proves the specification result;
nearby definitions and ingredients do not close it.

## Verification

- [Combined build and audit command receipts](EpistemicReports/ThroughWave2/VERIFICATION.json).
- [Cold project build receipt](EpistemicReports/ThroughWave2/COLD_BUILD_RECEIPT.json).
- [All 383 named theorem declarations](EpistemicReports/ThroughWave2/THEOREMS.json).
- [Exact combined #print axioms output](EpistemicReports/ThroughWave2/AXIOMS.txt).
- [Axiom totals, protected-file checks and source hashes](EpistemicReports/ThroughWave2/AUDIT_SUMMARY.json).

All 19 original protected files and all six original Wave 1 mathematics sources
are unchanged. Only new source files plus the new extension umbrella/audit and
reports were added or updated. HEAD remains bd80f4a on chile-epistemic-evolution,
with no commits ahead of origin/main. Nothing was pushed; no PR or remote change
was made.


## Wave 3 — compiled partial checkpoint, 2026-10-13

This appended section supersedes the historical “Wave 3 has not started” text
above. Earlier sections and all earlier source files have been preserved.
The five new mathematics modules compile in the finite umbrella. All 238 new
named theorems are audited; the combined audit now covers 621. Full specification
coverage remains partial, with omissions stated explicitly below.

### Exact result maps and conventions

The authoritative theorem-by-theorem maps, explicit hypotheses and deviations are:

- [SilentGene: clonal selection and crossings](EpistemicReports/Wave3/SILENT_GENE.md).
- [GenotypeTransition: actual parents, mutation, histograms and one-step levels](EpistemicReports/Wave3/GENOTYPE_TRANSITION.md).
- [CorrelatedAnswers: copies, covariances, empirical laws and witnesses](EpistemicReports/Wave3/CORRELATED_ANSWERS.md).
- [SpawnAllocation: certificates, Law2 lift, forecast and policy results](EpistemicReports/Wave3/SPAWN_ALLOCATION.md).
- [InnovationArrival: exact and conditional hazard results](EpistemicReports/Wave3/INNOVATION_ARRIVAL.md).

The following index covers Part C/D/E result families in both specifications.
Names have the namespace shown in the first column; the lane maps give every
auxiliary name and its exact hypotheses.

| Namespace / source result | Lean headline names | Current status |
|---|---|---|
| SilentGene — A C0/C1, B C.0/C.1 clonal identities | `silent_frequency_preserved`, `advocate_frequency_step`, `advocate_odds_step`, `clonal_mean` | Proved for actual Law1.step with positive fitness and relevant compartment positivity. Both voter genotypes have identical fitness; c is the resulting positive b+a. |
| SilentGene — A C1/C3, B C.2 finite trajectories and thresholds | `constant_fitness_closed_form`, `board_frequency_time`, `advocate_frequency_time`, `silent_frequency_time`, `advocate_odds_time`, `advocate_deficit_bound`, `board_deficit_bound`, `board_half_frequency_iff`, `advocate_half_frequency_iff` | Proved actual finite clonal orbit and bounds; no truncation-selection identification. |
| SilentGene — A C3, B C2e–g crossings | `CrossingModel.advocate_exists`, `.board_exists`, `.advocateTime_le_bernoulli`, `.boardTime_le_bernoulli`, `.board_before_advocate_iff` | Proved; Nat.find existence discharged using Bernoulli certificates. Ordering criterion retains 1<=advocateTime. |
| SilentGene — both crossing orders | `advocateFirstA_crossings`, `boardFirst_crossings`, `advocateFirstB_crossings` | Counterexamples / exact certificates for (4,1), (2,6), (3,2), evaluated with norm_num through the proved crossing criteria. |
| SilentGene — A C4, B C.5 removal does not imply silent suppression | `removing_voters_does_not_suppress_silent` | Counterexample on an actual normalized law: voter mass falls while conditional silent frequency remains1/2. |
| GenotypeTransition — A C2, B C.3 actual crossover | `independentRosterCrossover_mass`, `distinctRosterCrossover_mass`, `survivorLaw_mass`, `recombine_linkage` | Proved: actual Fin S×Fin S index laws, with/without diagonal; actual histogram/S, rho1/2 or S/(2(S-1)), preserved marginals and linkage factor1-rho. |
| GenotypeTransition — A C2.1, B C.4 mutation and elitism | `mutate_mass`, `mutate_voterMass`, `mutate_silent_coordinate`, `retainedOffspring_silentFrequency` | Proved normalized mutation rows, unchanged-elite mixture, boundary-safe coordinate formulas; conditional frequency carries positive voter mass. |
| GenotypeTransition — B C4f–g conditional finite histogram transition | `broodHistogram_mass`, `histogramKernel_mass`, `histogramKernel_expectedCount` | Proved actual finite IID-brood pushforward and history-conditioned survivor-law mixture; genotype counts are not asserted to be a Markov state. |
| GenotypeTransition — B C4e ratios | `ratio_expectation_counterexample`, `expectedRatio`, `ratioOfExpectations` | Counterexample: expected ratio1/2 differs from ratio of expectations1/4. Positive expected denominator explicit for the latter. |
| GenotypeTransition — G1 corrected priority and one-step1/15 | `protected_set_forces_zero_advocate_survivors`, `corrected_priority_actual_one_step_one_fifteenth` | Proved under explicit minimal protected-set rank priority, all-voter initial population, P12/S4/eight offspring, actual crossover and offspring-only A mutation1/10, B mutation disabled. Survivor conclusion is derived. |
| GenotypeTransition — A C4, G2 expected realized ratio | `all00_expected_silent_ratio`, `all00_actual_one_step_two_locus`, `all00_actual_distinct_one_step_two_locus` | Proved conditional on four00 survivors and eight IID offspring, both loci mutate1/10 in offspring only:3523336551/55000000000. Actual finite binomial formula then norm_num. |
| GenotypeTransition — G2 ratio of expected counts | `all00_one_step_ratio_of_expected_counts` | Proved9/140 for the same fixed survivor/product child law; separate from expected realized ratio, with positive expected voter count. |
| CorrelatedAnswers — A D1, B D.1 clones | `clone_variance`, `clone_chebyshev`, `natural_copies_bound`, `effectiveCopies_eq_iff` | Proved actual independent lineage-coordinate law; n_eff<=L with equality iff all positive natural clone counts equal. Reproved on main. |
| CorrelatedAnswers — A D2, B D.3 partial correlation | `correlated_variance`, `correlated_effective_identity`, `correlated_chebyshev`, `exchangeable_effective_size`, `correlatedEffectiveSize_le_sample_iff` | Proved actual finite covariance statements; variance interpretation requires0<p<1 and positive bracket. Equal-correlation specialization is algebraic. |
| CorrelatedAnswers — A D2, B D3d weighted extension | `weighted_correlated_variance`, `normalized_weighted_mean`, `weighted_effective_identity` | Proved; effective interpretation explicitly requires nonnegative sum-one weights and positive bracket. |
| CorrelatedAnswers — B D.4 higher-order witness | `same_independent_pairs`, `pair_covariances_zero`, `majority_accuracy_not_pairwise`, `pairwise_effective_size_three` | Counterexample: same complete pair tables and n_eff3, actual majority probabilities3/4 and1/4. |
| CorrelatedAnswers — referee G4 label witness | `correctness_pattern_does_not_determine_plurality` | Counterexample on actual ordered words: identical correctness pattern(1,0,0), duplicate wrong labels lose and split wrong labels win by first appearance. |
| CorrelatedAnswers — A D3, B D.2 empirical information | `empirical_squared_error`, `empirical_squared_error_le`, `empirical_concentration`, `empirical_concentration_simple` | Proved actual IID-law error expectation(1-sum pi²)/N<=1/N and finite bad-coordinate probability bound. |
| CorrelatedAnswers — A D3 biased binary example | `biased_binary_accuracy_bound`, `biased_binary_accuracy_min_bound` | Proved actual first-appearance plurality accuracy<=min(1,8/N) at correct mass1/3. |
| CorrelatedAnswers — A D3, B D.2 identification | `two_world_success_sum`, `two_world_nonidentification` | Proved for any common finite observation law and randomized response kernel; different designated correct labels have success sum<=1. Applies to actual IID samples of every size. |
| SpawnAllocation — A E1, B E.1 reach | `actual_reach_payoff`, `reach_marginal_identity`, `reach_marginals_nonneg`, `reach_marginals_decreasing`, `reach_endpoint_zero`, `reach_endpoint_one` | Proved actual IID reach-response bridge plus finite payoff/marginal identities, including p0/p1. Nonnegative/decreasing marginals require alpha>=beta. |
| SpawnAllocation — A E2, B E.3/G6 allocation | `greedy_pick_dominates_unpicked`, `dominating_bset_maximum`, `exists_certified_allocation`, `exists_optimal_reach_allocation`, `certified_reach_optimal` | Proved constructive threshold existence and global sufficiency with natural budget, unit slots, nonnegative marginals and per-task diminishing values. Prefix-slot allocations preserve task identity. |
| SpawnAllocation — A E2/B E.3/G7 slot dual | `item_dual_feasible`, `slot_lp_dual`, `slot_lp_dual_min`, `slot_certificate_value` | Proved per-item multipliers max(d-lambda,0), min(B,item count) version and attainment certificate; separate capped-slot constraint system. |
| SpawnAllocation — A E2/E3, B E.4 whole-allocation lift | `whole_allocation_kkt`, `whole_allocation_kkt_consequences` | Proved existing Law2.KKT on the subtype of complete feasible prefix allocations, full argmax-supported mass, c1/ell0/B1/Q0, mu=fmax andlambda0. |
| SpawnAllocation — A E1/B E.2/G5 nonconcavity | `posted_vote_increasing_marginals`, `fixed_benchmark_increasing_marginals` | Counterexamples on actual IID laws, explicitly zero abstention: vote accuracies3/5,3/5,81/125; actual fixed-common-pool rescue response0,0,p(1-p). |
| SpawnAllocation — A E3, B E.5 forecasts | `forecast_regret`, `forecast_gap_identifies`, `marginal_forecast_error`, `biased_forecast_two_task_A`, `biased_forecast_two_task_B` | Proved2epsilon regret and exact ex ante reach-objective arithmetic: loss1020/15625;63/50 versus119/100. The separate actual_reach_payoff theorem supplies the sampling bridge. No observed-draw adaptive forecast claim. |
| SpawnAllocation — A E3/B E.4–E.5/G8 policies | `clonal_policy_support`, `clonal_policy_ratio`, `suboptimal_mass_bound`, `supported_within_maximizers_equal_payoff`, `redrawn_policy_unchanged`, `redrawn_with_elites`, `biased_policy_ratio` | Proved actual clonal-policy finite bounds and inherited ratio(119/126)^t. Exact optimal support is worded within M; absent optima are not created. Independent redraw prevents inherited correction; elite retention is separate. |
| InnovationArrival — A B7.2, B E.6 arrival | `independent_no_appearance`, `independent_appearance`, `absence_eq_of_conditional`, `absence_le_of_conditional_lower`, `absence_ge_of_conditional_upper`, `appearance_le_trials_mul` | Proved actual independent finite-trial law and exact/upper/lower conditional-hazard versions, with appearance<=M*T*u. No establishment conclusion. |
| InnovationArrival — B E.6 zero-support | `selection_zero`, `selectionIter_zero`, `presence_le_appearance` | Proved mutation-free support invariance and separate present-event containment bound. |

All indices start at zero; positivity requirements are explicit. The two ratio
estimands remain separate. Realized ratios use the documented zero convention
on empty voter classes; the three illustrative states retain four voters and
have positive realized denominators. `rho` in GenotypeTransition means crossover;
`rho` in SpawnAllocation means a fitness-gap ratio, in separate namespaces.
`InnovationArrival`'s M is offspring trials per generation; the optimal strategy
set is `SpawnAllocation.maximizers`. No global overloaded abbreviation connects
them. c is the advocate-board fitness b+a and can be positive even when a<0.

### Not formalized: exact remaining objects

- SilentGene: separately named scalar-y sign/endpoints; analytic log/ceiling or
  limit corollaries. Actual coordinate update, odds and finite bounds are proved.
- GenotypeTransition: the displayed signed four-coordinate recombination
  formulas, conditional q/z formulas and effective recombination coefficient
  after elite mixing; the arbitrary-survivor conditional expected-ratio binomial
  formula; the separate uniform-slot/elite-fraction identification. Their
  additional coordinate/count-conditioning adapters are not installed.
- GenotypeTransition: full experimental evaluation/history metadata update and
  the lossless full-state projection C4h; deterministic multigeneration silent
  mutation recursion/fixed point, the all-individual mutation-order countermodel,
  the selection-plus-recombination numeric witness, and referee G3's t2 numerical
  refuter. These need separate lifecycle or history proofs. No prohibited
  multigeneration random-voter-slot assertion is made.
- CorrelatedAnswers: general B D2b wrong-mode polynomial bound, explicit
  clone-block reduction of the correlation denominator, and optional finite
  optimal-decision-value monotonicity. The required difference-variable, block
  counting and decision/prefix transports are not installed.
- SpawnAllocation: general fixed-benchmark/posted-vote/premium marginal identities
  E1c–g; the necessity/exchange-iff side of the allocation characterization;
  explicit conversion from a separately defined arbitrary feasible natural-vector
  type back to prefix sets; finite payoff-gap bound E4c and analytic limits.
  Certificate existence and global sufficiency on concrete prefix allocations are
  proved; no missing inverse or converse is silently claimed.
- InnovationArrival: complete replay matrix-power formula B7.1 and a concrete
  simulator metadata transition. The requested finite arrival theorems are proved.

Optional continuous analysis, Gaussian/Hoeffding refinements, and the continuous
PriceMarket envelope adapter are excluded. No PriceMarket.replication_wedge
adapter was introduced. The discrete finite payoff identity in SpawnAllocation
is explicitly its own algebraic statement.

### Verification and custody

[Wave 3 return](RETURN_EPISTEMIC_WAVE3.md),
[build and audit receipts](EpistemicReports/Wave3/VERIFICATION.json),
[238 new exact axiom outputs](EpistemicReports/Wave3/AXIOMS.txt),
[621 combined exact axiom outputs](EpistemicReports/ThroughWave3/AXIOMS.txt),
[source hashes, forbidden scan and preservation checks](EpistemicReports/Wave3/AUDIT_SUMMARY.json).

Wave3:234 theorems use the standard trio,4 use propext/Quot.sound.
Combined:614 standard trio,6 propext/Quot.sound,1 no axioms. No unexpected axiom.
All19 protected files and all14 earlier mathematics modules are unchanged.
Only permitted append-only integration touches earlier files. HEAD remains
bd80f4a on chile-epistemic-evolution; no commits, pushes, PRs or remote changes.
Stopped after Wave3; earlier-wave gaps remain for a later close-out pass.


Scope qualification from final independent review: `SpawnAllocation.maximizers
f fmax` is an equality level set. `supported_within_maximizers_equal_payoff`
proves E[f]=fmax for a law supported there; its interpretation as optimal payoff
requires a separately certified true maximum. The selection bound explicitly
carries hmax, and the whole-allocation KKT construction supplies a maximum
certificate. No maximality premise is hidden in the equality-level-set definition.
