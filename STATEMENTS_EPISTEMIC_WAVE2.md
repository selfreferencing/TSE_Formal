# Wave 2 statement ledger

Current compiled partial checkpoint. The two adopted mappings below give every
proved statement's Lean name and explicit hypotheses, and enumerate omissions.
These mappings supersede the historical Wave 1 “not started” entries for Part B.

- [Mutation and historical/current pooling](EpistemicReports/Wave2/MUTATION_AND_POOLING.md)
- [Selection, tie kernels, paired scores and noise](EpistemicReports/Wave2/SELECTION_AND_PAIRED_SCORES.md)
- [All 137 audited theorem names](EpistemicReports/Wave2/THEOREMS.json)
- [Exact per-theorem axiom output](EpistemicReports/Wave2/AXIOMS.txt)

## Binding interpretation

The full finite state type retains ordered roster, evaluation counters, histories,
and generation. Its normalization lemma composes supplied kernels; it is not an
implementation or a Markov-sufficiency proof for the whole simulator. Expected
survivor counts permit zero; `price_count_identity` uses no positive-propensity
selection-gain adapter.

Actual lexicographic sorting and all three normalized tie-key laws are defined.
The strict-outcome counts are proved and consumed by `implemented_topS_master`.
Conditional tied survivor counts remain explicit inputs. Fair balanced-count
results require the fair tied expectation, even P and 0<S<P. The protected-incumbent
correction is separate. Deriving the tied expectation from the implemented uniform
permutation law remains open.

The noisy-selection bound docstrings state that the advertised experimental
specializations are vacuous at n<=36 boards. IID paired scores use actual product
coordinates; the sharp half-factor bound includes the zero-minus-mass boundary.
No label is assigned a causal interpretation.

Historical pooling theorems concern actual strict-score events and an explicitly
defined share observable. The adapter to protected-incumbent top-S survival is
not proved. Numerical master-expression evaluations are algebraic instances;
they are not complete stochastic roster/key-law witnesses.

## Remaining unformalized work

The adopted mappings record source labels and individual obstacles for:

- Actual tied-count expectations for incumbent, uniform-slot and uniform-genotype
  key laws; their concrete numeric master realizations; the identical-outcome
  incumbent mutation floor and multi-generation comparison.
- Full experiment transition and count-state non-Markov witness; uniform-subset
  inclusion proof for the neutral baseline; general allele and binary-flip instances.
- General paired count/tie polynomials, even/odd tie positivity, n=12 -231/2048,
  fixed-discordance coupling and several additional numerical witnesses.
- Direct affine-survival covariance/Law1 specialization, full conditional total
  variance under task heterogeneity, and score-difference covariance theorem.
- Historical-pooling retention/sort adapter; separate mean/variance interpretation
  of the unequal-evaluation witness; mixture witnesses 46/165 and 3217/12300.
- Optional continuous scale-family, Gaussian, Hoeffding and limit results.

These omissions contain no admitted declarations and no conclusion-equivalent
hypotheses. They are deliberately absent from the imported sources.
