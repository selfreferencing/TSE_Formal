# FiniteProbability wave-1 module report

Date: 2026-10-12.
Source: `SEKernel/FiniteProbability.lean`.
Final compile: `lake build SEKernel.FiniteProbability`, exit 0 (10 seconds on final build).

## Implemented statements

All names below are under `SEKernel.FiniteProbability`; law theorems are under `Law`.

- Finite normalized laws: `Law` (mass, nonnegativity, total).
- Existing-kernel aliases: `Law.expect` is definitionally `Law1.mean`; `Law.variance` is definitionally `Law1.variance`.
- Finite probability, covariance, expectation algebra, event monotonicity, complements, binary and finite union bounds.
- Doc A F0 (0.1): `Law.total_expectation`, with a finite classification map describing the partition. `conditionalMean` uses zero on null cells; `prob_mul_conditionalMean` proves that this convention disappears after multiplication by cell mass.
- Finite Markov: `Law.markov` and `Law.markov_mul`.
- Doc A F0 (0.2): `Law.chebyshev`.
- Doc B B2.5 finite Cantelli ingredient: `Law.cantelli`, including zero variance.
- Product laws: `Law.prod` and dependent finite product `Law.pi`; `Law.expect_pi_prod` gives the general product-moment identity.
- Independence is represented by actual separate product coordinates: `Law.expect_pi_coord_mul`.
- Nonidentically distributed independent variance sum: `Law.variance_pi_sum`.
- Doc A F0 (0.3): `Law.iid_average`, with the explicit premise `0 < n`, proving both mean and variance of the iid empirical mean.
- Finite kernels: `Kernel`, `Kernel.comp`, and `Kernel.comp_mass`.
- Finite kernel application and deterministic pushforward: `Law.bind`, `Law.map`, `Law.expect_bind`, `Law.expect_map`.

## Status and deviations

All infrastructure above is proved and compiled. No statement was weakened or left unproved. The homogeneous sample-space form of `variance_pi_sum` covers each observable as a function of its own actual product coordinate; `Law.pi` and `expect_pi_prod` themselves allow dependent heterogeneous coordinate types. No unproved independence predicate is used.

The three-point geometric moment bound belongs to the separately owned `PluralityBounds.lean` implementation and is not claimed as a theorem in this module.

Only this new source file and this report were modified by this worker. Existing Lean modules, remotes, and branches were not changed. No custom axioms, incomplete proofs, native evaluation, or large finite decision procedures were used.

## Headline theorem axiom audit

Command: `lake env lean /tmp/TSE_FiniteProbability_Audit.lean`, exit 0.

```text
'SEKernel.FiniteProbability.Law.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_union_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_exists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.mass_eq_zero_of_prob_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_mul_conditionalMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.total_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.variance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.variance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.prob_le_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.markov' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.markov_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.shifted_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_pi_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_pi_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_pi_coord_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.variance_sum_of_uncorrelated' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.variance_pi_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.variance_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.iid_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.expect_prod_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Law.variance_prod_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.FiniteProbability.Kernel.comp_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
```
