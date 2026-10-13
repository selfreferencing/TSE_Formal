# Wave 3: SpawnAllocation

Status: compiled finite module, with explicit remaining source items below.
Only `SEKernel/SpawnAllocation.lean`, unique `scratch/wave3/spawn_*` receipts,
and this new report were written by this lane. Earlier source/report files,
Git state, and remotes were not changed.

## Verification

- `lake build SEKernel.SpawnAllocation` passed: `scratch/wave3/spawn_build_15.log`, final `Build completed successfully (7902 jobs).`
- Frozen source SHA256: `8eae69d364522b91737284d983cd04c611086382f032e5178b274142a31f2053`.
- All 69 named theorem declarations are listed in `scratch/wave3/spawn_theorems.json`; the audit input is `scratch/wave3/spawn_axioms_01.lean`, exact output `scratch/wave3/spawn_axioms_01.txt`.
- Exact all-theorem audit passed: **69 names**, **67** `[propext, Classical.choice, Quot.sound]` and **2** `[propext, Quot.sound]`; no unexpected axiom or error. Output names match the manifest exactly. Root's combined Wave3 umbrella/audit also passed with all 69 Spawn names included.
- Comment-stripped forbidden-construct scan passed: `scratch/wave3/spawn_forbidden_scan.txt`. No custom axiom, admitted proof, native evaluator, large finite decide, opaque/unsafe/external implementation, global instance declaration, or raised maxHeartbeats was used.
- Internal read-only second-agent source review found no material mathematical issue. This is not external referee acceptance.

## Representation and hypotheses

`CallSlot K` is the finite sigma type of a task and a call index `Fin (K j)`.
Indices start at zero. A `FeasibleAllocation K B` is the **subtype of concrete
prefix-closed finite call-slot sets** whose cardinality is at most natural budget
B. `taskCount` recovers the number of selected calls per task. `taskCount_sum`
identifies total calls with set cardinality, `taskCount_le_cap` proves caps,
`prefix_allocation_ext` proves injectivity of that projection, and
`reach_allocation_objective` identifies the slot-expanded sum with the sum of
per-task reach payoffs. A separate independently defined Nat-vector feasible
type and inverse constructor/bijection have not been installed. Optimality below
is explicitly over the concrete prefix-slot subtype, not over a separately
asserted Nat-vector interface.

The marginal value is `weight j * (alpha j-beta j) * p j * (1-p j)^r`.
`exists_optimal_reach_allocation` takes nonnegative weights,
`0 <= beta <= alpha <= 1`, and `p in [0,1]`. Its constructed allocation uses
`min(B,sum_j K j)` slots, including empty task sets, zero capacities, B=0,
zero-valued calls and p=0/p=1. The price is nonnegative and has the actual budget
complementarity equation. No LP strong-duality hypothesis is used.

## Source-result mapping

Names below have prefix `SEKernel.SpawnAllocation` unless stated otherwise.

| Source result | Lean names | Status and exact scope |
|---|---|---|
| Doc B E.1 (E1a); Doc A E1 reach-only specialization | `reachPayoff`, `reachResponseLaw`, `actual_reach_payoff` | Proved actual IID proposal law followed by a normalized alpha/beta Bernoulli response kernel. Both response rates in [0,1] are explicit. Correct-answer mass is the actual law mass; abstentions are allowed in this reach theorem. |
| Doc B E.1 (E1b); Doc A E1 geometric marginal | `reach_marginal_identity`, `reach_marginals_nonneg`, `reach_marginals_decreasing` | Proved. Nonnegativity/decrease use alpha>=beta and p in [0,1]. |
| k=0 and p=0/p=1 conventions | `reach_zero`, `reach_endpoint_zero`, `reach_endpoint_one` | Proved, including the first p=1 marginal and all later zero marginals. No inverse of a zero probability is used. |
| Finite telescoping and discrete benefit-minus-cost expression, B (E1h) | `reach_telescoping`, `finite_spawning_wedge` | Proved. The wedge is a new finite identity; no adapter or invocation of `PriceMarket.replication_wedge`. |
| Referee G6 first named lemma | `greedyPick`, `greedy_pick_dominates_unpicked` | Proved actual finite maximum-image choice is in the remaining set and dominates every remaining/unpicked item. No maximizing choice is assumed as a conclusion-shaped hypothesis. |
| Referee G6 second named lemma | `dominating_bset_maximum` | Proved a b-set dominating its complement maximizes the sum against sets of at most b elements. Nonnegative item values are explicit, covering fewer calls. |
| Doc A E2 / Doc B E.3 certificate sufficiency | `SlotCertificate`, `slot_certificate_value`, `slot_certificate_optimal`, `certified_allocation_optimal`, `certified_reach_optimal` | Proved actual selected/unused price inequalities, positive-price budget saturation, and domination of every feasible fractional slot choice / every concrete feasible prefix allocation. |
| Required certificate existence, not merely sufficiency | `rankedSlotSet_card`, `rankedSlotSet_dominates`, `selected_record_le_unselected`, `rankedSlotSet_prefix`, `dominating_set_has_certificate`, `exists_certified_allocation` | Proved by actual finite lexicographic sorting. Equal marginal values are tied by within-task index, preserving prefixes. Then a threshold is constructed; empty/full/slack-budget cases are proved separately. |
| Requested reach-model global optimum | `exists_reach_certified_allocation`, `exists_optimal_reach_allocation`, `callSlot_card`, `reach_allocation_objective` | Proved existence of a certified globally optimal reach allocation on the concrete prefix-slot feasible subtype. Budget is min(B,sum K); the actual task-count payoff is consumed by the final optimality theorem. A step-by-step repeated-greedy algorithm is intentionally not implemented. |
| Referee G7, capped-slot LP dual | `itemMultiplier`, `itemMultiplier_nonneg`, `item_dual_feasible`, `slot_lp_dual`, `slot_lp_dual_min` | Proved with explicit per-item multipliers max(d-lambda,0), z>=0, z<=1 and sum z<=B. The stronger effective-budget form uses min(B,item count). `slot_certificate_value` proves attainment, and existence of the prefix certificate gives integral attainment. This LP remains separate from the existing two-resource Law2 constraints. |
| Doc B E.4 / Doc A E2 whole-allocation Law2 lift | `feasible_allocation_nonempty`, `whole_allocation_kkt`, `whole_allocation_kkt_consequences` | Proved on the **subtype** of complete feasible prefix allocations: return f>0, c=1, load=0, B_LP=1, Q_LP=0; full probability vector, mu=fmax, lambda=0, support within the argmax. Actual `Law2.KKT.isLPOptimal`, reduced-return and Nash/LP equivalence are consumed. Positivity of every shifted fitness is an explicit model hypothesis. |
| Doc A E1 / Doc B E.2 first increasing-marginal witness; G5 | `readableBernoulli_no_abstention`, `binary_vote_one_probability`, `binary_vote_two_probability`, `binary_vote_three_probability`, `posted_vote_increasing_marginals` | Actual IID ordered-word law with pi(none)=0. First-appearance plurality accuracies are 3/5,3/5,81/125; the last increase is positive. The N=3 probability is evaluated through the existing proved binomial count-tail formula, not by assuming the cubic. Deterministic short-word winner/count lemmas are proved. |
| Doc B E.2 fixed two-voter benchmark witness; G5 | `fixedTwoRescueLaw_correctness`, `fixed_two_rescue_zero`, `fixed_two_rescue_one`, `fixed_two_rescue_two`, `fixed_benchmark_increasing_marginals` | Actual response law with keep=0, post=1, absent=0 on one fixed two-word comparator. Pi(none)=0 is explicit; p in (0,1). Exposing prefixes gives F0=F1=0 and F2=p(1-p)>0. The event probability uses product-coordinate factorization. |
| Doc B E.5 / Doc A E3 forecast regret | `forecast_regret`, `forecast_gap_identifies`, `marginal_forecast_error` | Proved uniform 2 epsilon regret for a forecast maximizer; a strict >2 epsilon true gap excludes a worse chosen payoff. Slotwise forecast error sums to B*epsilon_m under actual call budget and nonnegative epsilon_m. |
| Doc B E.5 biased forecasts | `biased_forecast_two_task_B` | Proved reach-objective arithmetic: true next marginals 4/25 versus 9/100; payoffs 63/50 versus 119/100; biased trap forecast 99/10000<9/100, gap 7/100. Per-task probability interpretation is supplied separately by `actual_reach_payoff`; no joint two-task output law or separately named forecast-choice algorithm is constructed. The call is allocated ex ante. |
| Doc A E3 biased forecasts | `biased_forecast_two_task_A` | Proved reach-objective arithmetic after five calls per task: 1024/15625 versus 4/15625, loss 1020/15625; supplied zero Trap forecast prefers the positive Easy marginal. Same separate actual per-task payoff adapter; no claim that modal bias forces this forecast. |
| Doc B E.4 (E4a); Doc A E3 finite trajectory | `SEKernel.SilentGene.clonalTrajectory`, `SEKernel.SilentGene.clonalTrajectory_step`, `SEKernel.SilentGene.constant_fitness_closed_form`; consumed by policy theorems | Actual normalized finite Law1 clonal orbit from the other Wave3 module. Complete allocation strategies can instantiate its arbitrary finite type; exact constant positive fitness, no mutation/crossover, are the model. |
| Doc B E.4 (E4b); Doc A E3 finite optimal-mass bound | `suboptimal_mass_bound` | Proved actual clonal trajectory mass outside the equality argmax <= ((1-s0)/s0)*rho^t. Explicit positive fmax, initial optimal mass s0>0, 0<=rho<1, global true-fitness upper bound and true suboptimal fitness <=rho*fmax are inputs. These are structural fitness/gap hypotheses, not an assumption of the desired mass bound. |
| Referee G8 qualified optimal support/payoff | `clonal_policy_support`, `supported_within_maximizers_equal_payoff` | Proved zero initial policies stay absent at every finite time. The equality-level-set lemma proves E f=fmax for a normalized policy law supported **within** {i | f i=fmax}; this lemma alone does not certify fmax as the true maximum. Its optimal/argmax interpretation additionally requires a separate upper-bound certificate (supplied by `suboptimal_mass_bound`'s hmax or the KKT witness output in their respective applications). No equality of support with all optima is claimed, and no missing initial optimum is reconstructed. A limit or limiting-support theorem is not installed. |
| Doc A E3 / Doc B E.5 inherited forecast ratios | `clonal_policy_ratio`, `biased_policy_fitness_pos`, `biased_policy_ratio` | Proved exact ratios on the actual clonal orbit. The B witness has factor (119/126)^t, with positive initial accurate-policy mass explicit. The formula remains valid if biased-policy mass is zero; positivity of both initial policies can additionally be imposed when interpreting competition between present policies. |
| Doc A E3 / Doc B E.5 nontransmission | `redrawn_policy_unchanged`, `redrawn_with_elites` | Proved constant conditional offspring policy law nu remains nu after arbitrary normalized parental selection. The elite term is a coordinate identity; no unbounded elite coefficient is presented as a probability law. No assertion that within-lifetime learning is impossible is made. |

## Explicit omissions and stop-rule obstacles

- General fixed-benchmark identities Doc B (E1c)-(E1d), Doc A E1's absolute marginal bound and independence factorization, and general posted-vote accuracy/premium identities (E1e)-(E1g): not formalized. Actual specific fixed-benchmark and posted-vote counterexamples are proved; a general nested-event/cell-increment interface was not installed. Existing abstract cell algebra is not silently substituted for it.
- Necessity of the last/next marginal exchange criterion and the full iff with lambda certificates: not formalized. This delivery proves certificate sufficiency, a constructed certificate for every requested reach-model instance, and its global optimum; it does not characterize every possible optimal allocation.
- The separate per-call-price stopping theorem, variable-cost greedy counterexample, and a separately defined Nat count-vector feasible type/inverse adapter: not formalized. The delivered allocation type is the concrete finite prefix-slot subtype and unit call costs are structural.
- The converse statement that *every* existing Law2 LP optimum has full mass and argmax support is not separately formalized. The constructed full-probability KKT witness and its LP/Nash/reduced-return consequences are proved.
- Doc B (E4c) finite expected **payoff-gap** bound: not formalized. The finite suboptimal-mass bound is proved; its additional return-range weighted expectation consumer was not installed. No mass bound is labeled a completed payoff-gap theorem.
- Unique-optimum convergence, limiting concentration within M intersect initial support, and all other analytic limits remain optional analysis. Finite zero-support preservation, actual trajectory, finite mass bound and equal-payoff support theorem are the delivered replacements.
- A separate formal policy-action interface for the shared-bias/no-variation observation is absent. The inherited-ratio theorem and exact reset-kernel countermodel carry the transmissible-policy hypotheses; no universal genetic or causal claim is made.

## Binding fixes and deviations

G5 uses actual abstention-free laws in both counterexamples. G6 has two explicitly
named lemmas and nonnegativity for comparisons with fewer calls. G7 exposes each
positive-part multiplier and the min-budget item count. G8 says supported within
the equality level set/equal payoff; interpreting M as argmax requires a certified
true maximum. It preserves absent policies and never claims all optimal types
remain present. The complete-allocation KKT lift uses the actual feasible
subtype and full normalization. No earlier-wave proof gap was attacked and no
continuous PriceMarket theorem was reused as a discrete spawning result.
