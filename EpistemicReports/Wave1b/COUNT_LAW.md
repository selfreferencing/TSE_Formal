# Wave 1b count-law return

Scope: new `SEKernel/CountProfileCombinatorics.lean` and `SEKernel/IIDCountLaw.lean` only. No existing kernel module, frozen Wave 1 module, umbrella, main audit, or repository remote was changed by this worker.

## Compiled results and interfaces

All names below are in `SEKernel.Epistemic`.

- `wordCount z b`, `countProfile z`, and `countFiber c` measure actual ordered words `Fin N → B`; `wordCount_eq_labelCount` identifies the option-alphabet counts with the established plurality API.
- `exists_perm_of_countProfile_eq` constructs a label-preserving positional equivalence from equal actual counts. `mem_count_orbit_iff` identifies the complete orbit with the count fiber.
- `countFiber_card_mul_factorials` proves `#fiber × ∏b (count b)! = N!` using Mathlib's proved label-preserving stabilizer cardinal and orbit-stabilizer theorem. `countFiber_card` proves the actual fiber cardinal is `Nat.multinomial univ (countProfile z)`.
- `exists_word_of_sum_counts` proves every natural count vector with sum `N` is realized. Thus the probability theorem has no hidden realizability premise.
- `iidAlphabetLaw π N` is the existing finite product law on a generic finite alphabet. Its option instance is definitionally the established `iidWordLaw`.
- `iidAlphabetLaw_mass` proves actual per-word mass is `∏b π.mass b ^ wordCount z b`.
- `iid_countProfile_probability_card` proves actual count-event probability is the actual fiber cardinal times the common per-word mass.
- `iid_countProfile_probability π c hc` proves `Pr(countProfile = c) = Nat.multinomial univ c × ∏b π_b^(c_b)` for `hc : ∑b c b = N`.
- `iid_countProfile_probability_factorial` gives the same actual probability as `(N! / ∏b (c_b)!) × ∏b π_b^(c_b)`, with the factorial ratio in `ℝ`.
- `iidWordLaw_countProfile_probability` exposes the existing option-word-law specialization.
- `iid_countProfile_event_probability_card` measures an arbitrary actual event inside the actual count fiber. `eventCountFiber c E` is the finite set it counts.
- `shuffledWord_atom_equal`, `shuffledWord_atom_probability`, and `shuffledWord_event_probability` prove uniform positional shuffling is uniform over the entire count fiber.
- `iid_conditional_count_uniform_shuffle` proves, for any event `E`, the actual IID conditional event probability on a positive count cell equals its actual uniform-shuffle probability.
- `iid_countProfile_event_probability_shuffle` is the unnormalized bridge `Pr(count cell ∧ E) = Pr(count cell) × Pr_uniformShuffle(E)`. It has no positivity hypothesis and therefore covers zero-mass cells directly.
- `iid_binary_count_probability` proves the actual binary-word law `Pr(count true = j) = choose N j × p^j × (1-p)^(N-j)` for `j ≤ N`, with `p = π.mass true`.
- `firstTInWord` is a total first-active-label function; it returns `none` exactly on words with no entry in the active set. `firstTInWord_shuffledWord` connects it to the prior permutation object.
- `iid_conditional_firstT_probability` closes the missing actual-IID counting lemma: given a positive count cell and nonempty active positions, the first label in `T` is `a ∈ T` with conditional probability `wordCount z a / #activePositions(z,T)`.
- `iid_conditional_first_position_probability` proves the fair-tie counting ingredient: given actual counts and `N > 0`, first-coordinate label probability is `wordCount z a / N`, hence `j/N` when the correct count is `j`.

## Scope, hypotheses, and source mapping

Doc B A3.1's multinomial mass ingredient and its conditional uniformity claim are proved, not assumed. Doc B A4.2 / Doc A A4's asserted first-`T` counting step is now proved for the actual IID conditional-count law, rather than only a separate permutation model. The A0–A5 referee's fixed-count `j/N` fairness ingredient is also proved.

The convention is `N ≥ 0`, with all valid natural count vectors including zero counts. Empty products and `0^0 = 1` retain Mathlib's usual conventions. The binary theorem states `j ≤ N`; the source's count-vector sum restriction supplies this condition. Conditional ratios require an explicit strictly positive count-event probability. The first-coordinate theorem additionally requires `0 < N`. No positivity of individual label masses is imposed on the unconditional formula or unnormalized bridge.

The full plurality tie-weight sum, overlapping-prefix joint sum, fair-tie majority identity, wrong-consensus polynomial, payoff polynomial sampling adapter, and numerical counterexamples are separate consumers, not claimed by these two files. They are assigned to other Wave 1b work; this worker has left no failed proof or unproved premise for its requested keystone statements.

## Validation

`lake build SEKernel.IIDCountLaw` completed successfully, compiling both new files and their dependencies. The final rebuild after the prose-comment token cleanup also completed successfully. All 29 theorem declarations were checked with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur; `sum_boolCountProfile` needs only `propext` and `Quot.sound`.

Strict forbidden-token scan of the final source is clean. There are no new global instances, opaque premises, evaluation-based proofs, or large finite decisions.

## Exact axiom output

```text
'SEKernel.Epistemic.wordCount_eq_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.wordCount_eq_card_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.sum_wordCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.wordCount_comp_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.exists_perm_of_countProfile_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.mem_count_orbit_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.countFiber_card_mul_factorials' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.countFiber_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.exists_word_of_sum_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.shuffledWord_countProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iidAlphabetLaw_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_countProfile_probability_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_countProfile_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_countProfile_probability_factorial' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iidWordLaw_countProfile_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_countProfile_event_probability_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.shuffledWord_atom_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.shuffledWord_atom_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.shuffledWord_event_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_conditional_count_uniform_shuffle' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.sum_boolCountProfile' depends on axioms: [propext, Quot.sound]
'SEKernel.Epistemic.countProfile_bool_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.multinomial_boolCountProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_binary_count_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstTInWord_shuffledWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_conditional_firstT_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstTInWord_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.iid_conditional_first_position_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SEKernel.Epistemic.iid_countProfile_event_probability_shuffle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
