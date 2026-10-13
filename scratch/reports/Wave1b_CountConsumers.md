# Wave 1b count consumers return

Scope: new `SEKernel/PluralityCountFormula.lean` and `SEKernel/PluralityCountExamples.lean`. This worker changed no frozen Wave 1/count-law file, original kernel file, umbrella, central audit/ledger, or remote. Both sources are frozen.

## Compiled mathematical results

All Lean names are in `SEKernel.Epistemic`.

- `candidatePositions_eq_active_modes` and `first_mode_iff_plurality` prove that the actual total ordered plurality rule is exactly first occurrence among the positive readable modes of the actual count vector.
- `active_modes_card` counts those positions as the number of tied modes times their common positive count. `shuffled_plurality_probability` consumes the proved first-`T` positional counting theorem to show the actual uniform-shuffle winner probability is `1 / #modes` for a tied mode, zero otherwise.
- `iid_countProfile_vote_probability` consumes the unconditional IID/shuffle bridge to give the actual joint count-cell/winner probability as multinomial mass times the tie weight. It needs only the valid count sum and applies to zero-mass count cells too.
- `plurality_multinomial_formula` proves **Doc B A3.1 in full** for the actual `voteAccuracy π N a`: sum over `validCountProfiles A N = piAntidiag univ N` of `Nat.multinomial univ c × ∏q π.mass q ^ c q` times the actual first-appearance tie weight. The factorial-ratio equality for this coefficient is already proved in `IIDCountLaw`/`CountProfileCombinatorics`. The marginal `1/m` ingredient of Doc A A6.1 is thereby closed; its prefix-conditional weights are separate remaining work.
- `prob_map_event`, `iid_map_atom_probability`, and `iid_map_event_probability` prove the finite IID mapping law. `labelFlag_mass` and `wordCount_labelFlag` identify a selected label's Boolean indicator law and its actual count.
- `iid_single_label_count_probability` derives the actual selected-label binomial count law from `iid_binary_count_probability`. `iid_single_label_tail_probability` gives its exact finite binomial tail, for every natural threshold and sample size (including an empty tail when threshold exceeds size).
- `iid_five_consensus_polynomial` proves the actual three-of-five consensus probability `10q^3 - 15q^4 + 6q^5`. `iid_five_falseConsensus_polynomial` combines the proved disjoint-consensus partition with that actual tail to close **Doc B A4.4 / A4.7**.
- `actual_trap_correctMode_B` defines an actual law with correct mass `3/5`, wrong mass `2/5`, no abstention, and proves its wrong-consensus probability `992/3125 > 3/10` together with its correct strict-mode certificate.
- `actual_trap_correctMode_A` similarly proves **Doc A A3.6**: correct `11/20`, wrong `9/20`, actual wrong-consensus probability `650997/1600000 > 3/10`, with a correct strict mode.
- `actual_nonTrap_wrongMode_A` defines the actual seven-readable-label law with correct `1/5`, one wrong `3/10`, five further wrong labels `1/10` each; it proves wrong-consensus probability `5147/25000 < 3/10` and proves the distinguished wrong label is a strict mode among all readable labels.

Every numerical probability above is evaluated with `norm_num` after rewriting by the proved actual count-tail/polynomial theorem. No numerical theorem evaluates the ordered word space or a large finite decision procedure.

## Conventions and deviations

`N` and thresholds range over all natural numbers, including zero, matching Doc B. `readableModes c` contains precisely the positive readable maxima. Doc B's displayed `H(c)` also contains zero-count labels in an all-abstention profile, but explicitly assigns that case zero success weight. Our set is empty in that case and gives the same zero weight. This makes the empty readable alphabet and `N=0` cases total without a maximum over an empty set. Zero label masses and `0^0 = 1` retain Mathlib's conventions.

The full plurality formula is unconditional and does not reuse its uniform tie weight after conditioning on a posted prefix. The actual-IID conditional count bridge and `j/N` first-coordinate counting lemma are already proved in `IIDCountLaw`; this lane does not claim the general voter-count cancellation identity from them.

## Explicit remaining gaps

- **Not formalized in this lane:** Doc A/Doc B two-block overlapping vote/post count law, including the conditional prefix-weight rule and Doc A A6.1's `d_m/m`, `(1-d_m)/m` weights. The needed first-`T` counting and conditional-count shuffle lemmas exist, but the concatenation/two-block product-law transport has not been constructed here.
- **Not formalized in this lane:** the general binary identity `V_(2k) = V_(2k-1)`. The actual binomial/count law and fair first-coordinate counting ingredients exist; the finite-sum cancellation is not proved here.
- **Not formalized in this lane:** actual nonmodal plurality numerical witnesses `(3/8,1/8,1/2)` and `(2/5,1/2,1/10)` at their specified sizes, and the size-interaction numerical examples. The general actual plurality count formula is proved. A bounded diagnostic attempted explicit small count-profile enumeration; it was stopped at the parent's report/freeze instruction before a checked enumeration receipt or numerical consequence existed. No diagnostic theorem was adopted or exported.
- **Not claimed:** the sampling adapter for the ten-draw/five-post hump. It needs the unresolved overlapping-prefix law or a separate direct positional counting argument.

The optional scope above was stopped rather than weakened. There are no equivalent-conclusion hypotheses or unproved counting assumptions in the compiled files.

## Validation

`lake build SEKernel.PluralityCountFormula` exited 0 (`Build completed successfully (7895 jobs)`). `lake build SEKernel.PluralityCountExamples` exited 0 (`Build completed successfully (7896 jobs)`). Logs are `scratch/logs/pluralitycount_build.log` and `scratch/logs/pluralityexamples_build.log`.

The final strict source-token scan found no occurrences of `sorry`, `admit`, custom-axiom declarations, `native_decide`, or `decide`. No new global instance or opaque premise was introduced. Minor unused-simp linter warnings do not affect compilation.

Full theorem names: `scratch/reports/Wave1b_CountConsumers_TheoremNames.txt` (23 declarations).

Axiom audit: `lake env lean scratch/checks/count_consumers_axioms.lean` exited 0. All 23 declarations report exactly `[propext, Classical.choice, Quot.sound]`; full receipt is `scratch/logs/count_consumers_axioms.log`.

## Frozen source hashes

- `SEKernel/PluralityCountFormula.lean`: 211 lines; SHA256 `4b33a7a2617c48fb22b1b5b9da24a6d3df4c0e405ee28052ceac54f4262aca34`.
- `SEKernel/PluralityCountExamples.lean`: 225 lines; SHA256 `d4ac5cae160cb1b019d676f09b585af06bab80f14351d796fa1273dcf34736dd`.

## Exact axiom output

```text
'SEKernel.Epistemic.candidatePositions_eq_active_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.first_mode_iff_plurality' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_mem_readableModes' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.readableModes_equal_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.active_modes_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.shuffled_plurality_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_countProfile_vote_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.plurality_multinomial_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_map_event' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_map_atom_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.law_eq_of_mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_map_event_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelFlag_eq_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.labelFlag_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.wordCount_labelFlag' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_single_label_count_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_value_mem_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_single_label_tail_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_five_consensus_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_five_falseConsensus_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.actual_trap_correctMode_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.actual_trap_correctMode_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.actual_nonTrap_wrongMode_A' depends on axioms: [propext, Classical.choice, Quot.sound]
```
