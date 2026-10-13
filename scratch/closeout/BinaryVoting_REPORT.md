# Close-out: BinaryVoting report

Module: `SEKernel/CloseoutBinaryVoting.lean` (namespace `SEKernel.Closeout.BinaryVoting`,
1174 lines, SHA-256 `8b9924026c78d0968895c32ab910756c0c32af58df7bde91168becada2e2c313`).
Imports `SEKernel.PluralityCountExamples` and `SEKernel.EpistemicPayoff` only. No other
repository file was modified; scratch work is under `scratch/closeout/binaryvoting/`.
Not added to the umbrella (`EpistemicFinite`) or the central axiom audit: that is the
integrator's step.

All probabilities are probabilities of the actual IID ordered-word law (`iidWordLaw`) under
the actual first-appearance plurality rule (`voteAccuracy`, `reachProbability`). Binary
law = any `π : Law (Option Bool)` with `π.mass none = 0`, correct label `a`, `p = π.mass (some a)`.

## Results

| # | Target | Lean theorem(s) | Exact statement gist | Status |
|---|---|---|---|---|
| 1 | Binary vote formula | `binary_vote_formula`, `binary_vote_formula₀`, `voteAccuracy_eq_binaryVotePoly` | For `N ≥ 1`: `voteAccuracy π N a = Σ_(j<N+1) C(N,j) p^j (1-p)^(N-j) w_N(j)`, `w = 1` if `2j>N`, `1/2` if `2j=N`, else `0`. `₀` version holds for every `N` (incl. 0) with the tie weight requiring `j>0`. Derived from `plurality_multinomial_formula` (zero-abstention profiles reindexed by `j`; multinomial = `C(N,j)`; tie factor from `readableModes`). | proved |
| 2 | Fair ties | `binary_fair_ties` (algebraic core `binaryVotePoly_fair_ties`) | `1 ≤ k → voteAccuracy π (2k) a = voteAccuracy π (2k-1) a`. Proof: count formula's `1/2` tie weight (which comes from the proved first-tied-label counting, the `j/n` fact) + Pascal's rule; the two boundary terms cancel by `C(2m+1,m+1) = C(2m+1,m)`. | proved |
| 3 | Hump identification | `binary_hump_identification`, `binary_ten_vote_eq_nine`, `idealRecognizer_premium_hump`, `binary_hump_bounds`; also `rRecognizer_premium`, `rRecognizer_premium_pos_iff` | `reachProbability π 10 5 a - voteAccuracy π 10 a = hump10 p` (via `V_10 = V_9 = binaryVote9 p` and `hump_reach_vote_polynomial`; `V_10 = binaryVote9` also checked directly). Ideal recognizer = prefix kernel outputting `some a` iff the posted 5-prefix contains `a` (else abstains); its premium (`ordered_response_premium_eq`) is `hump10 p`. Bounds `0 ≤ D ≤ 5p`, `D ≤ 10(1-p)` (A5.2). `r`-recognizer: `D_r = r R - V`, `D_r > 0 ↔ V/R < r` and `V/R < 1` for `0<p<1` (A5.3-A5.4). | proved |
| 4 | Union bound | `one_sub_voteAccuracy_le`, `ten_voter_union_bound` | Any finite alphabet, any law: `0 < N → 1 - voteAccuracy π N a ≤ N (1 - π.mass (some a))`; and `1 - V_10 ≤ 10(1-p)`. `N ≥ 1` is necessary (at `N=0` LHS is 1). | proved |
| 5 | Prefix realizability | `prefix_keep_one_forces_post_one`, `binary_10_5_keep_one_forces_post_one`, `binary_10_5_no_keep_one_post_lt_one` | Prefix-only = `prefixLift hk R` (response law at a full word is `R (postedWord z k)`, so output and internal randomness are functions of the first `k` draws). Binary law, `0<p<1`, 10/5: if `responseRates … .keep = 1` then `correctness R a w = 1` for every readable prefix `w` containing `a`, and `responseRates … .post = 1`; hence keep=1 with post<1 is impossible. General version: `k ≤ N`, `1 ≤ k`, `2k ≤ N+1`, `3 ≤ N`. Keep/post cells are proved to have positive mass, so the null-cell default never enters. Prefixes containing abstentions have probability 0 and are left unconstrained. | proved |
| 6 | Nonmodal counterexamples | `three_label_vote_formula`, `three_label_V2/V3/V4`, `nonmodal_B_values`, `nonmodal_A_values` | Three readable labels, no abstention: `V_2 = p`, `V_3 = p^3+3p^2(q+r)+2pqr`, `V_4 = p^4+4p^3(q+r)+3p^2(q^2+r^2)+12p^2qr` from the count formula. Law `(3/8,1/8,1/2)`: `V_2=3/8, V_3=93/256, V_4=189/512`. Law `(2/5,1/2,1/10)`: `V_2=2/5, V_3=49/125, V_4=2/5`. Both: `V_3 < V_2`, `V_3 < V_4`, wrong strict mode. | proved |
| 7 | Chance pickup (Doc A A2) | `uniformPick_accuracy`, `chance_pickup_example` | Uniformly picking one of `k` posted IID answers has accuracy exactly `p` (any law). Law `p=1/4` (binary, no abstention): `V_3 = 5/32`, random-posted accuracy `1/4`, premium (actual `ordered_response_premium_eq`) `= 3/32`. | proved |

Nothing in the target list was left unformalized. No statement carries a hypothesis that
assumes its conclusion. The only side conditions are those the mathematics needs:
`N ≥ 1` (targets 1 and 4), `0<p<1` and `N ≥ 3` (target 5, for positive cell masses).

## Compile

`export PATH="$HOME/.elan/bin:$PATH"; cd ~/Desktop/TSE_Formal_chile; lake env lean SEKernel/CloseoutBinaryVoting.lean`
exits **0** with no errors and no warnings. Token scan of the final file: no `sorry`, `admit`,
`native_decide`, `decide`, `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`, `instance`,
`set_option` or `maxHeartbeats`.

## Axiom check (`scratch/closeout/binaryvoting/AxCheck.lean`, exit 0, all 88 declarations)

Every declaration depends on `[propext, Classical.choice, Quot.sound]` or a subset.

```text
'SEKernel.Closeout.BinaryVoting.binaryProfile' does not depend on any axioms
'SEKernel.Closeout.BinaryVoting.binaryVoteWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryVoteWeight₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.wrong_mass_of_no_abstention' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.multinomial_binaryProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.prod_binaryProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.mem_readableModes_binaryProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.tie_binaryProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.prod_eq_zero_of_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryProfile_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.sum_validCountProfiles_binary' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_vote_formula₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryVoteWeight₀_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_vote_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binomTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryVotePoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binomTerm_pascal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binomTerm_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.weight_even_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.fair_tie_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryVotePoly_fair_ties' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.voteAccuracy_eq_binaryVotePoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_fair_ties' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryVotePoly_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binaryVotePoly_ten' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.coord_ne_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.all_correct_vote' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.one_sub_voteAccuracy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.ten_voter_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_hump_identification' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_ten_vote_eq_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.pointLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.prefixLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.idealRecognizer' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.idealRecognizer_correctness' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.idealRecognizer_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.idealRecognizer_premium_hump' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.hump10_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_hump_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.answerWithProb' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.rRecognizer' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.rRecognizer_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.rRecognizer_premium' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.rRecognizer_premium_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.iidWordLaw_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.readable_of_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.mass_le_prob' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.eq_one_of_responseMass_eq_cellMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.responseMass_eq_cellMass_of_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.strict_count_winner' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.extendCorrect' does not depend on any axioms
'SEKernel.Closeout.BinaryVoting.postedWord_extendCorrect' depends on axioms: [propext, Quot.sound]
'SEKernel.Closeout.BinaryVoting.suffixPositions_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.extendCorrect_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.extendCorrect_vote' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.extendCorrect_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.cellOf_post_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.keep_cell_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.oneCorrectFirst' does not depend on any axioms
'SEKernel.Closeout.BinaryVoting.oneCorrectFirst_not_vote' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.oneCorrectFirst_reaches' depends on axioms: [propext, Quot.sound]
'SEKernel.Closeout.BinaryVoting.post_cell_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.prefix_keep_one_forces_post_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_10_5_keep_one_forces_post_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.binary_10_5_no_keep_one_post_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.prof3' depends on axioms: [propext]
'SEKernel.Closeout.BinaryVoting.tieWeight3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.multinomial_prof3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.mem_readableModes_prof3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.card_readableModes_prof3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.tie_prof3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.pairs3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.sum_validCountProfiles_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.three_label_vote_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.three_label_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.three_label_V2' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.three_label_V3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.three_label_V4' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.threeLabelLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.nonmodalLawB' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.nonmodalLawA' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.nonmodal_B_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.nonmodal_A_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.uniformPick' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.coord_eq_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.uniformPick_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.chanceLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.BinaryVoting.chance_pickup_example' depends on axioms: [propext, Classical.choice, Quot.sound]
```
