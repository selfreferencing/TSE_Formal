# Genotype transition: Wave 3 return

Compiled and frozen new module `SEKernel/GenotypeTransition.lean` only. The module has 856 lines and 63 named theorems. All names below are in `SEKernel.GenotypeTransition`.

No earlier source, central umbrella/audit/ledger, Git state, or remote was changed by this worker. All listed inputs were read before writing Lean: Doc B C/D/E and plan/interfaces; Doc A B7/C/D/E; all referee G1–G8; original handoff Wave 3; operative `TASK_CONSTRAINTS.md`; current ledger and Wave 2 return/mapping. No document code was executed.

## Mathematical results and source map

| Specification result | Lean name(s) | Status and precise scope |
|---|---|---|
| Four genotype law, marginal/compartment masses | `Genotype`, `boardMass`, `advocateMass`, `voterMass`, `four_masses_sum`, `voterMass_eq_one_sub_boardMass` | Proved finite-law normalization identities; genotype is `Bool × Bool`, board bit first. |
| Doc B C3a / Doc A C2 linkage determinant | `linkage_determinant` | Proved: `D = q11 − QB QA = q00 q11 − q01 q10`. |
| General rho recombination | `recombine`, `recombine_mass` | Normalized finite law for `0 ≤ rho ≤ 1`, with every genotype mass equal to `(1-rho)q + rho(qB × qA)`. |
| Preserved marginals and linkage | `recombine_boardMass`, `recombine_advocateMass`, `recombine_linkage` | Proved: both allele marginals are preserved and `D_R = (1-rho)D`. |
| Actual independent locus-choice coins | `pairCrossover`, `pairCrossover_mass` | Actual pushforward of uniform `Bool × Bool` coins; the four parental-locus combinations each receive weight 1/4. |
| Doc B C3b / Doc A C2 independent parents | `independentCrossover_mass`, `independentRosterCrossover_mass` | Proved for a genotype law and for actual uniform `Fin S × Fin S` survivor index pairs, including the diagonal: rho = 1/2. The actual survivor law is `survivorLaw`; `survivorLaw_mass` proves its histogram/S mass for `S > 0`. |
| Doc B C3f / Doc A C2 distinct parents | `distinctPairLaw`, `distinctPair_expect`, `distinctRosterCrossover_mass`, `distinctRho_bounds` | Actual uniform ordered pair law with zero diagonal mass, normalized for `S > 1`; every child genotype mass equals recombination with rho = `S / (2(S-1))`, which lies in [0,1]. |
| Doc B C4a / Doc A C2.1 mutation matrix | `flipLaw_mass`, `mutationKernel`, `mutate_mass` | Actual normalized per-locus flip laws, product mutation rows, and finite total-probability sum over parental genotype. Both mutation rates are explicitly in [0,1]. |
| Doc B C4c boundary-safe formulas | `mutate_voterMass`, `mutate_silent_coordinate` | Proved voter mass and 01-coordinate formulas without dividing by a possibly empty compartment. These apply at both role boundaries. |
| Doc B C4b/C4d elite/offspring mixture and conditional ratio | `retainedOffspringLaw`, `retainedOffspring_silentFrequency` | Normalized slot-mixture law with unchanged elites and offspring-only mutation; its conditional silent-frequency formula carries a strictly positive voter-mass hypothesis. The general finite-population count first moment is proved separately below; a uniform-slot adapter identifying `elite = S/(S+M)` is not separately installed. |
| Doc B C4f full conditional histogram law | `Histogram`, `histogram`, `nextRoster`, `broodHistogramLaw`, `broodHistogram_mass`, `histogramKernel_mass` | Proved actual finite histogram pushforward of an IID offspring word, then mixture over a full-history-indexed ordered-survivor kernel. The state type and selected-survivor kernel remain explicit inputs; genotype histograms are not declared sufficient Markov states. |
| Doc B C4g histogram first moment | `broodHistogram_expectedCount`, `histogramKernel_expectedCount` | Proved `E N'_g = s_g + M h_g`, followed by expectation over the history-conditioned selection law. |
| Connection to actual selected subsets | `selectedRoster`, `rosterSelectionLaw` | Actual deterministic roster from a cardinality-S survivor subset in original index order, and normalized pushforward of an actual subset-selection law. |
| Doc B C4e expected ratio differs from ratio of expectations | `ratio_expectation_counterexample` | Genuine finite two-count-outcome law: expectation of realized ratio is 1/2, ratio of expectations is 1/4. `expectedRatio` and `ratioOfExpectations` are separate objects; the latter explicitly requires positive expected voter count. |
| Actual one-step expected silent ratio, all-00 survivors | `iid_product_expectation`, `all00_inner_expectation`, `all00_expected_silent_ratio` | Proved from actual IID product coordinates, regrouped into independent board/advocate word laws. Inner advocate expectation gives `muA J/(S+J)`; the proved binomial count law then gives the exact finite sum. This is an expected realized ratio, not a ratio of expected counts. Empty voter classes use the explicitly documented zero convention. |
| G2 one-step 1/15 ingredient | `all00_one_step_one_fifteenth` | Actual fixed-survivor expectation: four retained 00, eight offspring, no B mutation, A mutation 1/10; proved by the exact finite count formula then `norm_num`. |
| Minimal corrected G1 rank-priority implication | `lexSurvivors_record_top`, `protected_set_forces_zero_advocate_survivors`, `protected_set_selectedRoster_all00` | Proved for the actual lexicographic sorter. A protected set T with at least S members must have A=0 and rank before every A=1 individual. Other A=0 individuals may rank anywhere. The theorem derives the all-zero advocate survivor state; it does not assume that conclusion. The all-00 conclusion also requires the all-voter initial model. |
| Corrected G1/G2 one-step 1/15 | `corrected_priority_actual_one_step_one_fifteenth` | Exact P=12, S=4, eight-offspring theorem: minimal protected-set priority, all voters, actual independent survivor-index crossover, offspring-only advocate mutation 1/10, disabled B mutation. All-00 survivors are derived from actual sorting. |
| G2 one-step 3523336551/55000000000 | `all00_one_step_two_locus_expected_ratio`, `all00_actual_one_step_two_locus`, `all00_actual_distinct_one_step_two_locus` | Proved actual expected realized ratio, conditional on four all-00 survivors and eight conditionally independent offspring. Both loci flip at 1/10 in offspring only. Actual independent and distinct parent protocols are both connected to the product child law via `all00_independentCrossover_law`, `all00_distinctCrossover_law`, and `mutate_point00_law`. |
| G2 ratio-of-expected-counts value 9/140 | `all00_one_step_ratio_of_expected_counts` | Proved actual IID product-offspring expectation with the same four-00/eight-offspring state. Expected voter count is explicitly proved positive; the ratio is 9/140. It is separate from the preceding expected ratio. The product child law is the proved all-00 crossover-plus-mutation law. |
| G3 one-step scope | All numerical and `nextSilentExpectation` results above | Only one step conditional on specified survivors is claimed. No random-voter-slot multigeneration assertion is made. |

The stronger convenience lemmas `priority_forces_zero_advocate_survivors`, `priority_selectedRoster_all00`, and `priority_one_step_one_fifteenth` require every A=0 individual to rank before every A=1 individual. They are valid sufficient special cases; the later `protected_set_*` and `corrected_priority_actual_one_step_one_fifteenth` supply the exact minimal referee hypothesis. The older convenience theorem permits an input roster of size P and creates twelve next slots; only the final corrected theorem fixes both the experiment's input and output size to twelve.

## Explicit omissions and boundaries

- **Not formalized:** full protocol history-update transition C4h / the complete experimental replay B7. The supplied full-history-indexed survivor law and actual histogram projection are formalized, but no concrete evaluation/history metadata successor function, full-state kernel, or lossless projection theorem is installed here. No genotype-only Markov claim is made.
- **Not formalized separately:** Doc B C3c's signed four-coordinate `±rho D` display, C3d/C3e and Doc A C2's conditional q/z recombination formulas, and the effective recombination coefficient after retaining an arbitrary elite fraction. The normalized recombination mass formula, preserved marginals and linkage identity are proved; no missing displayed consumer is counted as closed by those nearby ingredients.
- **Not formalized:** the arbitrary-survivor-state conditional expected-ratio binomial formula from Doc A C4. The exact actual expectation is defined for arbitrary survivor rosters and a full histogram kernel is proved; the binomial reduction is proved only for the all-00 fixed survivor state needed for the illustrative levels. General composition/conditioning on the random voter denominator remains unconstructed.
- **Not formalized:** the deterministic multigeneration mutation recursion C5a/C5b, its fixed-point/closed-solution instantiation, Doc A C4's all-individual selection/recombination/mutation lower-bound countermodel, and Doc B C5's numeric selection-plus-recombination silent-frequency counterexample. These need additional coordinate/trajectory consumers; this lane does not substitute scalar definitions or recurrence conclusions as hypotheses.
- **Not formalized:** the referee G3 multigeneration numerical refuter 37/100 versus 73/200. The prohibited generalization is avoided by restricting all illustrative finite-population statements to one step.
- Clonal selection `z'=z`, odds, and crossing certificates belong to `SilentGene`; no claim about their implementation is made by this lane report.

Conditional probability/expected-ratio denominators follow two explicit conventions: compartment frequencies such as `silentFrequency` require a positive voter mass; realized population ratios use zero when no voter exists. A voter-present conditional scientific estimand would additionally require a positive voter-presence probability and is not claimed here. All illustrative states have four retained voters, so their realized denominators are nonzero.

## Verification and custody

Final named build: `PATH="$HOME/.elan/bin:$PATH" lake build SEKernel.GenotypeTransition`, exit 0, `Build completed successfully (7899 jobs)`. Receipt: `scratch/wave3/genotype_build_09.log`. The source is frozen at SHA256 `aa6dd4ade43a4e093ce237e000b9f8e0c6451afb15835cc8fde726c1e0f57ab1`.

The strict final source-token scan is clean for prohibited declarations/proof constructs, including finite `decide`, custom axioms, evaluation-based proofs, and heartbeat overrides. No global instance is added. Minor non-fatal linter warnings remain.

All 63 theorem names: `scratch/wave3/genotype_theorem_names.txt`. `lake env lean scratch/wave3/genotype_axioms.lean` exited 0. Every one of the 63 named declarations reports exactly `[propext, Classical.choice, Quot.sound]`; no other axiom occurs. Exact receipt: `scratch/wave3/genotype_axioms.log`.

## Exact axiom output for all 63 named theorems

```text
'SEKernel.GenotypeTransition.four_masses_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.voterMass_eq_one_sub_boardMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.linkage_determinant' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.marginal_fst_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.marginal_snd_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.recombine_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.recombine_boardMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.recombine_advocateMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.recombine_linkage' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.pairCrossover_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.independentCrossover_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.survivorLaw_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.expect_prod_iterated' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.prod_map_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.independentRosterCrossover_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.flipLaw_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.mutate_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.mutate_voterMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.mutate_silent_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.retainedOffspring_silentFrequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.distinctPair_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.pairCrossover_diagonal_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.independentRoster_mass_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.survivorLaw_mass_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.distinctRho_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.distinctRosterCrossover_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.wordCount_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.wordCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.wordCount_real_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.nextRoster_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.broodHistogram_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.iid_offspring_count_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.broodHistogram_expectedCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.histogramKernel_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.histogramKernel_expectedCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.ratio_expectation_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.iid_product_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.expect_count_function' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.voterCountR_eq_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.silentCountR_eq_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_inner_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_expected_silent_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_one_step_one_fifteenth' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_one_step_two_locus_expected_ratio' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.nextRoster_silentCountR' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.nextRoster_voterCountR' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.iid_silentCountR_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.iid_voterCountR_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_one_step_ratio_of_expected_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.lexSurvivors_record_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.priority_forces_zero_advocate_survivors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.priority_selectedRoster_all00' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.priority_one_step_one_fifteenth' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.constant_bind_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_independentCrossover_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_distinctCrossover_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.mutate_point00_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_actual_one_step_two_locus' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.GenotypeTransition.all00_actual_distinct_one_step_two_locus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.protected_set_forces_zero_advocate_survivors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.protected_set_selectedRoster_all00' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.GenotypeTransition.corrected_priority_actual_one_step_one_fifteenth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
