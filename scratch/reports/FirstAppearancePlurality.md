# FirstAppearancePlurality — Wave 1 worker return

Owner scope: only `SEKernel/FirstAppearancePlurality.lean` and this report.
All of Doc A and both assigned Part A referee files were read before Lean edits;
the manager opened the all-input gate after its complementary source reads.
No code from a specification was executed.

## Representation and convention

Namespace: `SEKernel.Epistemic`. Ordered words are `Fin N → Option A`.
Both `N = 0` and `k = 0` are allowed. Probability formulas for a prefix carry
`k ≤ N` explicitly. Abstention is `none`; answer labels need no order.
Plurality finds the least position among positive readable maximal-count
positions. Relabelling is a genuine equivalence of the option alphabets fixing
`none`; it preserves the actual selected position.

## Proved interfaces and statements

| Source/result | Lean name | Scope |
|---|---|---|
| Ordered count | `labelCount`, `labelCount_eq_sum`, `labelCount_pos_iff` | Actual ordered-word counts, not a replacement distribution |
| Total first-appearance plurality | `plurality`, `plurality_eq_none_iff`, `plurality_empty` | Returns `none` exactly on all-abstention words |
| Relabelling gate | `labelCount_relabel`, `candidatePositions_relabel`, `plurality_relabel` | Full option-alphabet equivalence fixing abstention |
| Winner semantics | `plurality_mem_word`, `plurality_maximal_count`, `plurality_dominates_readable`, `plurality_first_maximal` | Occurrence, maximality, and least maximal position |
| Unique readable label | `plurality_unique_readable` | Every readable occurrence has the same label |
| Comparator and prefix | `correctVote`, `reaches`, `comparatorCell`, the three `comparatorCell_*_iff` lemmas | Exact deterministic cells |
| V need not imply prefix reach | `correctVote_need_not_reach_prefix` | Concrete `(none, correct)` length-two word |
| Strict-majority consensus | `consensusAt`, `consensus_unique` | Carries `N < 2 * threshold` |
| Whole-word consensus cells | `consensusCell`, four `consensusCell_*_iff` lemmas, `consensusCellProbability_total`, `falseConsensus_probability_cells` | Consensus counts all of input z; k only controls reach. Probabilities exhaust that whole-word-consensus experiment. |
| Actual posted prefix | `postedWord`, `postedWord_labelCount`, `postedWord_reaches_full` | Restricts a length-N word to its first k positions with explicit k ≤ N; counts proved equal to the full-word filter i < k |
| Posted-prefix consensus cells | `prefixConsensusCell`, `prefix_consensus_unique`, four `prefixConsensusCell_*_iff` lemmas, `prefixConsensusCellProbability_total`, `prefix_falseConsensus_probability_cells` | Counts exactly the posted prefix; uniqueness uses k < 2 * threshold, so five posts/threshold three is covered even with N = 10 comparator draws; cell probabilities are under the full-word law |
| False consensus partition | `falseConsensus_probability_eq_sum` | Actual probability is the disjoint sum of wrong-label threshold probabilities |
| Independent ordered law | `iidWordLaw`, `prob_pi_forall` | Product of separate coordinates; rectangle factorization proved |
| Missing-answer probability | `no_appearance_probability` | `(1 - π.mass a)^N` |
| Reach | `reach_full_probability`, `reach_prefix_probability` | `1 - (1 - π.mass (some a))^k` |
| Empty comparator | `voteAccuracy_zero` | Actual voting accuracy at zero length is zero |
| Full reach necessity | `correctVote_reaches_full`, `voteAccuracy_le_reach_full` | Does not claim prefix necessity |
| Zero-mass labels | `zero_mass_reach`, `zero_mass_voteAccuracy` | Zero probability of appearance/winning; full alphabet-padding adapter is not yet proved |
| Comparator-cell normalization | `cellProbability_total`, `cellProbability_keep` | Actual cell probabilities sum to one |
| Overlap accounting | `jointVote_partition`, `cellProbability_posted`, `cellProbability_absent` | `V=vR+vU`, posted=`reach-vR`, absent=`1-reach-vU` |

All proofs use the actual finite laws and total plurality definition. No
uniformity, multinomial-count, or joint-law theorem is assumed as a premise.

## Not formalized in this module

| Required result | Exact obstacle / next work |
|---|---|
| First T-labelled entry has conditional probability `u_a/L` | Requires a new finite counting/orbit argument on ordered words with fixed counts. A valid route marks one T-occurrence and compares word/permutation fibers while retaining non-T positions. Searches of Mathlib's multinomial, list-permutation and finite-cardinality APIs found algebraic multinomial identities, but no ready ordered-word fiber-count result. The missing exchangeability assertion was not installed as an equivalent hypothesis. |
| Multinomial plurality count formula | Depends on fixed-count word enumeration plus the first-T lemma. The actual law is defined and its semantics proved, but a definition or ordered enumeration is not recorded as the requested count formula. |
| Full two-block overlapping joint count law | The exact event identities are proved. The multinomial `W(u,v) g(u,v)` formulas still require the previous counting bridge. |
| Five-post consensus probabilities and false-consensus polynomial | The actual disjoint-event probability identity is proved. The binomial count distribution and hence `10q^3 - 15q^4 + 6q^5` probability formula are not linked to the ordered law here. |
| Fair binary ties and `V_(2k) = V_(2k-1)` | Requires the fixed-count first-coordinate probability `j/n`; not assumed. |
| Invariance after adjoining a new zero-mass label | Appearance and winning have zero probability for zero-mass labels. A full pushforward/embedding invariance theorem remains separate. |

The general count and exchangeability gap is recorded explicitly. It is not
silently transferred to an interface premise, and later algebraic evaluations
must not be reported as ordered-experiment counterexamples without the missing
probability bridge.

### Follow-up counting result

A subsequent bounded attempt produced and compiled the separate
`FirstTiedLabelCounting.lean` module. Its `firstTLabel_probability` proves the
`u_a/L` formula on the genuine uniform-permutation law of a fixed ordered word,
with least-index semantics and count preservation. See
`scratch/reports/FirstTiedLabelCounting.md`. The remaining gap is the bridge from
an IID law conditional on its count vector to that shuffle pushforward, and the
multinomial enumeration; the first-label permutation-counting step itself is
now proved.

## Validation

Build and headline axiom receipts are supplied to the manager after the last
source change. The manager owns the integrated umbrella and final audit.

Review correction: the original `consensusCell` docstring incorrectly suggested
that its consensus counts used the prefix. Its definition always counted the
entire supplied word. The docstring is corrected, the generic definition is
preserved, and the explicit `postedWord` / `prefixConsensusCell` adapter now
formalizes consensus on the posted pool. Historical audit output below predates
this narrow adapter patch; a fresh patch audit is appended afterward.


Final worker validation: `lake build SEKernel.FirstAppearancePlurality` exited 0 after the last source edit. The following audit covers all 45 theorem declarations; Lean audit exit code 0.

```text
'SEKernel.Epistemic.labelCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.candidatePositions_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.candidatePositions_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_mem_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_maximal_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_dominates_readable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_first_maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_unique_readable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.comparatorCell_keep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.comparatorCell_posted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.comparatorCell_absent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.reaches_zero' depends on axioms: [propext, Quot.sound]
'SEKernel.Epistemic.correctVote_reaches_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.correctVote_need_not_reach_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_disjoint_sum_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensus_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.falseConsensus_not_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_correct_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_wrongPosted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_wrongAbsent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_noConsensus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.falseConsensus_probability_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.falseConsensus_probability_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_pi_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_single_label_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.no_appearance_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.reach_full_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixPositions_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.reach_prefix_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.voteAccuracy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.voteAccuracy_le_reach_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.zero_mass_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.zero_mass_voteAccuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_keep' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.jointVote_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_posted' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_absent' depends on axioms: [propext, Classical.choice, Quot.sound]
```


Posted-prefix correction validation: `lake build SEKernel.FirstAppearancePlurality` exited 0 after the final adapter edit. All 54 theorem declarations re-audited; Lean audit exit code 0. This supersedes the earlier 45-theorem audit.

```text
'SEKernel.Epistemic.labelCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.candidatePositions_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.candidatePositions_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_mem_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_maximal_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_dominates_readable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_first_maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_unique_readable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.postedWord_reaches_full' does not depend on any axioms
'SEKernel.Epistemic.postedWord_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.comparatorCell_keep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.comparatorCell_posted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.comparatorCell_absent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.reaches_zero' depends on axioms: [propext, Quot.sound]
'SEKernel.Epistemic.correctVote_reaches_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.correctVote_need_not_reach_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelCount_disjoint_sum_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensus_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.falseConsensus_not_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_correct_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_wrongPosted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_wrongAbsent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCell_noConsensus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.consensusCellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefix_consensus_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixConsensusCell_correct_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixConsensusCell_wrongPosted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixConsensusCell_wrongAbsent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixConsensusCell_noConsensus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixConsensusCellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefix_falseConsensus_probability_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.falseConsensus_probability_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.falseConsensus_probability_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_pi_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_single_label_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.no_appearance_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.reach_full_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prefixPositions_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.reach_prefix_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.voteAccuracy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.voteAccuracy_le_reach_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.zero_mass_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.zero_mass_voteAccuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_keep' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.jointVote_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_posted' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.cellProbability_absent' depends on axioms: [propext, Classical.choice, Quot.sound]
```
