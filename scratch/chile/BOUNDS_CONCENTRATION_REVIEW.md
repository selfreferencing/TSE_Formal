# Wave 1: bounds and concentration implementation record

Source review: all of Doc B (2,398 lines) and PROOFCHECK_B.md read. No embedded specification code was executed. Parent read the remaining mandatory inputs before opening the implementation gate.

Index convention: N and posted size include zero. Answer words retain order. Abstention is `none`. A bound on all-abstention outcomes is handled explicitly rather than treating abstention as a readable label.

## PluralityBounds

Namespace `SEKernel.Epistemic`.

- Doc B A3.2: `iid_count_geometric_bound` and `iid_count_rational_bound` prove the requested actual ordered-word tail. `countTailCoefficient higher lower` is `(higher-lower)^2/(2*(higher+lower))`. `countTailCoefficient_bounds` proves positivity and the upper bound 1/2 under the finite-law hypotheses.
- The proof constructs the per-draw multiplier `countTilt`, proves its exact product as powers of the actual label counts, proves that product at least one on the count event, calculates the one-draw moment, applies finite product expectation factorization and finite Markov. The moment is proved, not a supplied premise.
- The finite rational replacement is `geometric_mul_affine_le_one` / `geometric_le_rational`, by induction for N >= 0.
- Doc B A3.3 wrong larger mode: `wrong_mode_geometric_bound` and `wrong_mode_rational_bound`. The bridge to the actual winner is `readable_winner_dominates`, which handles absent competing labels.
- Doc B A3.3 strict correct mode: `correct_mode_geometric_bound` and `correct_mode_rational_bound` give sums over the actual wrong readable label subtype. `failed_vote_count_witness` handles both all-abstention and N=0 using the explicit nonempty wrong-label hypothesis. Correct mass positivity remains explicit at the public interfaces.
- Common positive lower bound on the coefficients: `correct_mode_common_rational_bound`; explicit cutoff `correct_mode_cutoff`. The supplied positive `a0` is a numeric lower bound on each coefficient, not an assumed probability inequality. This avoids introducing a hidden minimum or dividing by a possibly zero mass.
- One-readable-label case: `sole_readable_accuracy` proves exactly `1-(1-p)^N` under `Subsingleton A`.

Not formalized in this bounded wave:

- A3 tied-mode symmetry/completion. Requires label-permutation invariance of the complete product law plus a finite tied-set orbit argument.
- A3.4 weak-mode monotonicity and the quantitative abstention correction. The artificial-relabelling prior, likelihood-pairing maximum theorem and decision-value marginalization bridge are not installed. No monotonicity claim is made from a tail bound.
- A3.5 / Doc A nonmodal numerical counterexamples as actual plurality probabilities. The general multinomial count formula is not installed; symbolic polynomials without that bridge would not prove the requested counterexamples. No large finite decision procedure was substituted.
- Optional second-moment count bounds and limits. The general finite Chebyshev/Cantelli layer exists separately; these particular count instantiations are not installed here. Hoeffding remains outside this T1 module.

## PluralityConcentration

Namespace `SEKernel.EpistemicConcentration`.

- Doc B A6.1 concrete coupling: `central_word_mass_balancing`. Words are literally `Fin s -> Fin 3`; L/M/H count and every position are retained. `reflect` swaps L and H, is an involution, and transports all three counts. `wordMass_counts` proves product factorization, including zero masses. `wordMass_reflect_ge` compares each loss word to its explicit gain word. The summation proof uses `Finset.sum_bij` on loss/gain words.
- Doc B A6.1 layer cake: `symmetric_layer_cake` proves the exact finite telescoping identity. `symmetric_word_mass_balancing` consumes it and the reflection inequality for every symmetric reward increasing toward the center.
- `balancingLaw` is a proved normalized finite law with coordinate masses theta, eta-theta, 1-eta. `central_probability_balancing` and `symmetric_expectation_balancing` express the coupling conclusions as actual finite probabilities/expectations of X=#L and Y=#L+#M under its IID product law.
- Zero-mass label boundary: `zero_label_word_mass` and `zero_label_event_restriction`. Every word containing a null label has product mass zero, so restricting any event to null-label-free words leaves its probability exactly unchanged. No null-event conditional law is used.

Not formalized in this bounded wave:

- A6.1's explicit binomial-coefficient formula bridge from the coupled Bernoulli count to the printed sum. The independent-coordinate coupling result itself is proved.
- A6.2 collapsed-word factorization and exact first-occurrence success fractions for tied wildcard labels. It requires counting the tie-history-preserving conditional word fibers; reflection alone does not establish this consumer.
- A6.3 the sorted-list HLP transfer construction. No installed general-majorization result or unproved HLP input was used.
- A6.4 fixed-size voting/cell/premium majorization theorem. It requires BOTH preceding missing bridges. The result must use fixed PARAMETER constants kappa in [0,1]^3; a fixed response kernel's conditional means cannot be substituted without a separate invariance hypothesis.
- A6.5 / Doc A size-interaction counterexamples as actual plurality probabilities, for the missing count-law bridge already noted above.

No custom axiom, sorry, admit, native_decide, opaque premise constant, unproved global instance, or decision procedure over a large finite type is used. Only these new modules and scratch/reports were edited by this worker.

## Verification receipts

- `lake build SEKernel.PluralityBounds SEKernel.PluralityConcentration`: exit 0; both new modules built. Bounds emits only unused-hypothesis/style warnings. The explicit positive-correct-mass public hypotheses were deliberately retained.
- `lake env lean scratch/chile/AuditBoundsConcentration.lean`: exit 0. This audits all 39 named theorems in both files, not just the headlines. Every output is exactly the allowed set `[propext, Classical.choice, Quot.sound]`.
- Full raw output: `scratch/chile/AXIOMS_BOUNDS_CONCENTRATION.txt`.
- Source scan for `sorry`, `admit`, `native_decide`, custom `axiom`, opaque declarations or instances in the two modules: no matches.
