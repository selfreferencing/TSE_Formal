# Wave 3: CorrelatedAnswers

`SEKernel.CorrelatedAnswers` compiles, with 44 named theorem declarations.
[Final build](CORRELATED_ANSWERS_BUILD.log),
[all names and source hash](CORRELATED_ANSWERS_THEOREMS.json),
[exact #print axioms](CORRELATED_ANSWERS_AXIOMS.txt),
[audit receipt](CORRELATED_ANSWERS_VERIFICATION.json).

This module imports main-branch finite-law infrastructure and no JuryInversion
or other unmerged side-branch theorem. Trial and generation counts include zero;
results concerning empirical averages require strictly positive sample size.

## Source mapping

All names have prefix `SEKernel.CorrelatedAnswers.`.

| Specification | Lean names | Status / scope |
|---|---|---|
| A D1 / B D1a: clone variance | `cloneLaw`, `cloneAverage`, `clone_mean`, `clone_variance` | Proved for actual separate-coordinate Bernoulli lineages with deterministic copy weights. Natural positive multiplicities specialize the real weights; positive total is explicit for the mean. |
| A D1 / B D1a: effective copies <= lineages, balanced equality | `pair_square_identity`, `effectiveCopies_le`, `effectiveCopies_eq_iff`, `natural_copies_bound` | Proved on main. Natural-copy theorem states L>0 and each multiplicity>0; equality iff all multiplicities equal. No unmerged dependency. |
| B D1b: clone concentration | `clone_chebyshev` | Proved under explicit nonzero total/square sum and epsilon>0. Actual clone law; no independence of clones within a lineage is asserted. |
| A D2 / B D3a–b: partial-correlation variance and effective size | `variance_sum_covariance`, `covariance_off_diagonal`, `binary_variance`, `correlationSum`, `correlated_variance`, `correlated_effective_identity` | Proved for actual finite observables taking values 0 or 1 and common mean p. The variance interpretation explicitly requires 0<p<1; effective identity additionally requires the bracket>0. |
| B D3c exchangeable formula | `exchangeable_effective_size` | Proved algebraic specialization under equal supplied off-diagonal covariance ratios and positive bracket. Its Bernoulli variance interpretation uses the main theorem's additional common-mean, binary-value and 0<p<1 hypotheses. |
| A D2 / B D3d weighted form | `covariance_const_mul`, `weighted_variance_upper_triangle`, `normalized_weighted_mean`, `weighted_correlated_variance`, `weighted_effective_identity` | Proved actual finite weighted variance. The effective interpretation explicitly carries nonnegative sum-one weights, 0<p<1 and positive weighted bracket. |
| B D3 Chebyshev and n_eff<=n qualification | `correlated_mean`, `correlated_chebyshev`, `correlatedEffectiveSize_le_sample_iff` | Proved; n_eff<=n iff upper-triangle correlation sum>=0, with n>0 and positive bracket. No independent-tail substitution is inferred. |
| B D4 pairwise data do not determine majority accuracy | `even_pair_data`, `odd_pair_data`, `same_independent_pairs`, `pair_covariances_zero`, `majority_accuracy_not_pairwise`, `pairwise_effective_size_three` | Counterexample on actual uniform four-outcome laws. Every binary pair table is the independent fair table, n_eff=3 in each world, but majority probabilities are 3/4 and 1/4. Exact finite formulas evaluated with norm_num. |
| Referee G4 correctness pattern does not determine plurality | `correctness_pattern_does_not_determine_plurality` | Counterexample for actual ordered plurality: (correct,b,b) selects b; (correct,b,c) selects correct, with identical (1,0,0) correctness pattern. `plurality_at_first_candidate` connects the witnesses to the existing selector. |
| A D3 / B D2a distribution-estimation moments | `indicator_mean`, `empirical_moments`, `empirical_squared_error`, `empirical_squared_error_le` | Proved on actual IID product law: mean squared distribution error=(1-sum pi_a^2)/N<=1/N. |
| A D3 / B D2a finite empirical concentration | `empirical_concentration`, `empirical_concentration_simple` | Proved: event exists a with error>=epsilon has probability <=(1-sum pi_a^2)/(N epsilon^2)<=1/(N epsilon^2). This states the bad-coordinate event directly, avoiding an empty-alphabet maximum convention. |
| A D3 actual wrong-mode example | `binary_vote_requires_half`, `biased_binary_accuracy_bound`, `biased_binary_accuracy_min_bound` | Proved for actual independent binary readable words with correct mass1/3 and wrong mass2/3: accuracy<=min(1,8/N). The true finite first-appearance plurality is used. |
| A D3 / B D2 two-world identification limit | `two_world_success_sum`, `two_world_nonidentification` | Proved for any common finite observation law and any randomized response kernel: successes for different correct labels sum<=1, so one<=1/2. In particular the common law can be the actual IID answer law at any sample size. |
| General finite covariance ingredients | `covariance_symm`, `covariance_self`; Bernoulli moments `bernoulli_bit_mean`, `bernoulli_bit_variance` | Proved. |

## Not formalized

- B D2b's general wrong-mode polynomial bound with numerator p+q-delta^2.
  The two-label-difference variance/containment adapter was not installed;
  the requested actual 8/N binary example and earlier geometric modal bounds
  are proved separately and are not silently substituted for that formula.
- The explicit reduction of the general partial-correlation denominator to
  sum k_i^2 for clone blocks. Both underlying variance formulas are proved,
  but the block-index counting bridge is not installed.
- B D2's optional finite optimal-decision-value monotonicity theorem.
  It needs a finite decision-maximizer and sample-prefix transport proof;
  no decision-value definition or proof was added in this bounded pass.
- Analytic limits and independent exponential tails with an effective count
  substituted for sample size. The latter is not justified by second moments.

The weighted helper was independently compiled in scratch, then adopted and
recompiled in this production module. An internal independent source review
found no material semantic issue. This is not external referee acceptance.
