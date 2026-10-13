# First-T-labelled entry counting: bounded follow-up

File: `SEKernel/FirstTiedLabelCounting.lean`.
Namespace: `SEKernel.Epistemic`.

The sample space is the finite set of permutations of original positions
`Fin N`. `uniformLaw` gives each permutation the mass `1 / card(Perm(Fin N))`;
normalization is proved. A permutation maps original identities to shuffled
ranks. `shuffledWord z π k = z (π.symm k)` is the actual shuffled word.

The selector `firstActive S hS π` is the original position having least shuffled
rank among the active original positions `S`. Its membership and minimality are
proved. Swapping two active original identities gives a bijection of the entire
permutation sample space, preserving the active set and swapping the selected
identity. Uniform-law invariance therefore makes all active-identity atom
probabilities equal. Their finite sum is one, proving each is `1 / S.card`.

## Headline results

- `firstActive_uniform`: every active original identity is first with probability
  `1 / S.card`.
- `firstActive_label_probability`: the first active label equals `a` with
  probability `(S.filter (fun i => z i = a)).card / S.card`.
- `firstTLabel_semantics`: the returned label occurs at the least index of the
  shuffled word whose label belongs to `T`.
- `firstTLabel_probability`: for `a ∈ T` and at least one T-labelled position,
  the probability is
  `(univ.filter (fun i => z i = a)).card / (univ.filter (fun i => z i ∈ T)).card`.
  This is the requested `u_a / L` formula on a uniformly shuffled fixed word.
- `shuffledWord_labelCount`: every original label count survives shuffling.

No uniformity, conditional probability, or first-label distribution was assumed
as a theorem premise. The hypotheses are only finite objects, nonempty active
positions, and membership of the target label in T.

## Remaining boundary

This proves the first-label counting step under the genuine uniform-permutation
arrangement law. It does not yet identify an IID law conditional on its count
vector with the shuffle pushforward, nor enumerate the distinct count-vector
word fibers by multinomial coefficients. The multinomial plurality and
overlapping count formulas therefore remain unformalized. This distinction
must remain in the integrated statements ledger.

Build and all-theorem axiom receipts follow below after the final source edit.


Final worker validation: `lake build SEKernel.FirstTiedLabelCounting` exited 0 after the final source edit. All 13 theorem declarations audited; Lean audit exit code 0.

```text
'SEKernel.Epistemic.uniformLaw_prob_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_eq_of_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.swap_mem_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_atom_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.prob_mem_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstActive_label_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstTLabel_semantics' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.firstTLabel_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Epistemic.shuffledWord_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound]
```
