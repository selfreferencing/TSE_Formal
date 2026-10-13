# Close-out: selection layer (`SEKernel/CloseoutSelection.lean`)

Namespace `SEKernel.Closeout.Selection`. 2,371 lines, 114 theorems. Only this module, this report, and scratch files under `scratch/closeout/selection/` were created. No other file was modified, deleted or moved. No git write. No `lake build`.

- **Compile:** `lake env lean SEKernel/CloseoutSelection.lean` exits **0** with no errors and no warnings. Log: `scratch/closeout/selection/compile_final.log`.
- **Axioms:** `scratch/closeout/selection/AxCheck.lean` is a verbatim copy plus 114 `#print axioms` lines; it exits **0**. Results, all within the standard trio:
  - 111 theorems: `[propext, Classical.choice, Quot.sound]`
  - 2 theorems: `[propext, Quot.sound]` (`survivors_nonempty`, `incumbent_prio`)
  - 1 theorem: `[propext]` (`incumbentEvals_spec`)
  - Full output: `scratch/closeout/selection/AXIOMS.txt`.
- **Forbidden scan:** 0 hits for `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`, `instance`, `set_option`, `maxHeartbeats`, `maxRecDepth`. `decide` is used only on 12-element `Fin 12` filter cardinalities and on `true ≠ false`.
- **SHA-256:** `985ba03c0dbc3c005e111e7fce5ca09231000ff05a683758877e0371bee65a26`.

**Survivor sets.** Every survivor set is produced by the actual `lexSurvivors` sort. The "actual law" in each theorem is one of:
- `L.bind (fun ω => K (pooledScore roster g (sA ω) (sB ω)))`, with `K` one of `slotTieSelectionLaw`, `incumbentSelectionLaw`, `genotypeTieSelectionLaw`, or a general `tieSelectionLaw`;
- the product-space `implementedPooledExperiment`.

## Results

| Target | Lean theorem(s) | Statement gist | Status |
|---|---|---|---|
| Infrastructure | `lexSurvivors_cross`, `cross_set_unique`, `cross_target_count`, `lexSurvivors_const`, `count_of_precedes`, `count_of_follows` | Retained slots strictly precede discarded ones in record order. A block that precedes (follows) its complement keeps `min S K` (`S-(P-K)`). A complete tie does not depend on the tied score value. | proved |
| 1(i) slot ties | `slot_tied_survivors`, `uniform_perm_coord`, `slot_tied_count` | Under a tie and permutation π, the survivors are `{i : π i < S}`. Each coordinate of a uniform permutation is uniform. Expected tied count = `S·(K/P)`. | proved |
| 1(ii) incumbency | `incumbent_tied_count_A`, `incumbent_tied_count_B` | Strict evaluation priority for `g` gives tied count `H = min S K`; priority for the other block gives `L = S-(P-K)`. | proved |
| 1(iii) genotype coin | `genotype_tied_count` | With exactly two genotypes present, the expected tied count under a uniform genotype permutation is `(H+L)/2`. | proved |
| 1, list order (extra) | `listOrder_tied_survivors`, `listOrder_tied_count` | With a constant key, a tie keeps slots `0..S-1`. | proved |
| 1, master for the actual laws | `conditional_count`, `pooled_master`, `pooled_master_count`, `slot_master`, `incumbent_master_A`, `incumbent_master_B`, `genotype_master` | `E[Y] = (r₊H + r₋L + τ·T_A)/S` for the composite score-then-kernel law, with `T_A` = `Sx`, `H`, `L` or `(H+L)/2`. No hypothesis on `τ`. | proved |
| 1, `T_A` of `implemented_topS_master` | `product_tieCount`, `tieCount_of_const`, `slot_implemented_master`, `genotype_implemented_master`, `incumbent_implemented_master_A`, `incumbent_implemented_master_B` | `tieCount = T_A` on the score ⊗ key product space, and the existing master is instantiated. This form needs `τ ≠ 0`, because the conditional mean is 0/0 otherwise. | proved |
| 2a, neutral newcomer | `neutral_newcomer_share`, `neutral_newcomer_witness_slot`, `neutral_newcomer_witness_incumbent`, `fairBoard_probs` | With one copy among 12, `S = 4`, `P(tie) = 0` and `r₊ = r₋`, any key kernel gives `E Y = 1/8 > 1/12` and `E N = 1/2 > 1/3`. Concrete witness: a fair complementary board. | proved |
| 2b, 10/2 example | `block_fitness_decline`, `block_fitness_decline_slot`, `majorityRoster_share` | Unbiased scores (`E sA = 51/100`, `E sB = 49/100`) and no ties give `E Y = 151/200`, and expected true survivor-mean change `= -47/30000` (via `price_count_identity`). | proved |
| 2, extras | `twelve_order_probs`, `twelve_board_newcomer`, `twelve_board_balanced_incumbent`, `worse_type_can_increase`, `balanced_incumbent_witness`, `genotype_coin_share_witness` | Twelve fair boards: `τ = 231/1024`; slot ties give `947/8192`; incumbency gives `793/8192`; the balanced incumbent case gives `-231/2048`. Doc A's `9/80` and `71/80`. The referee's balanced case gives `-1/5` against `+1/20` (slot ties and genotype coin). Shares `1/4` against `1/6`. | proved |
| 3, one generation | `identical_outcomes_no_board`, `generation_expected_share`, `incumbent_mutation_floor`, `slot_ties_restore_baseline`, `genotype_coin_breaks_baseline`, `selection_control_contrast` | With identical scores, voters given priority by evaluations, and at least `S` voters, no board survives and `E X' = r·u`. Uniform slot ties give `E Y = x` and `E X' = affineStep r u d x` (the baseline). The genotype coin retains 1 board, not 2/3. B2.10: the contrast is `β(EY - x)`. | proved |
| 3, multi-generation | `nextRoster`, `genKernel`, `crossoverOff`, `crossoverOff_mean`, `genKernel_share`, `chainLaw`, `floor_chain_support`, `floor_chain_share`, `control_chain_share`, `floor_vs_control_instance`, `floor_vs_control_voterFirst`, `floor_below_control`, `floorSel_incumbent`, `incumbent_prio` | The kernel on phenotype rosters is: actual sort, then explicit offspring (two iid uniform survivor parents, a fair crossover coin, then mutation). Results: the invariant "at least `S` voters" holds at every generation; `E X_{t+1} = r·u`; the control mean is `meanTrajectory`. Instance: the floor is `2/25` at every `t ≥ 1`, equals the control at `t = 1`, and is strictly below `(5/6)(1-(113/125)^t)` for `t ≥ 2`. | proved |
| 4, historical pooling | `historical_sort_retains_iff`, `historical_actual_share`, `current_pool_newcomer_never_survives`, `historical_actual_instance` | Pointwise, the actual protected-incumbent sort keeps the newcomer iff ScorePooling's strict-win event holds. Consequences: `E[count/S] = E newcomerSurvivorShare = ½(1-2^{-m})/S`; current-pool ranking gives 0; the instance gives `3/32 > 1/12`. | proved |
| 5 | `total_variance`, `task_heterogeneity_variance`, `survivor_covariance_identity`, `affine_survival_variance`, `rosterFreq_sum` | Law of total variance for `bind`. A B6.2: `Var(Δ̂) = (Var_τ Δ(t) + E_τ σ²(t))/n`. B5.1: `E f̄_surv - f̄ = Cov_x(f,r)/r̄`, with zero weights allowed. B5.2: affine weights give `b·Var_x(f)/r̄`. | proved |
| B3.1 extra | `slot_minus_incumbent_actual`, `tie_penalty_pos`, `balanced_iid_sign` | On the actual laws, slot ties minus incumbency equals `τ(x - L/S)`, which is strictly positive at interior `K` and `S`. Balanced iid sign: `E Y > 1/2 ↔ b < a`, with the fair `T_A` derived rather than assumed. | proved |

## Boundaries (stated, not hidden)

- **Offspring in the one-generation theorems.** `generationLaw` uses the MutationBaseline interface: an offspring is a board with probability `mutationProbability u d y`. The chain uses explicit crossover, and `crossoverOff_mean` derives that marginal. Parents are drawn with replacement. Only the phenotype locus is tracked.
- **Chain priority.** "Voter-first in every state" is a hypothesis, as in Doc B ("if the priority persists"). `floorSel_incumbent` identifies it with `incumbentSelectionLaw` when evaluations are a function of the state. The evolution of evaluation counts is not modeled.
- **Order of retained survivors.** The next roster places the retained survivors in a fixed enumeration of the survivor set, not in rank order. Counts do not depend on this order.
- **Slot-tie law.** Per-slot inclusion `S/P` and expected counts are proved. Uniformity over `S`-subsets as a distribution is not.
- **Scores in `balanced_iid_sign`.** Scores are A-only and B-only win counts. Boards that both genotypes get right, or both get wrong, shift both scores equally.
- **Not formalized:** distinct-ordered-parent sampling; general tie polynomials in `n` beyond `n = 1, 12`; full simulator transition with evaluation and history counters.
