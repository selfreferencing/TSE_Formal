# Wave 1 return — Chile epistemic evolution

Prepared 2026-10-12. **Compiled partial Wave 1; the full requested Wave 1
mathematics is not closed.** This is the required stop-and-report checkpoint.
Waves 2 and 3 have not started. Nothing was pushed, no PR/repository was created,
and no remote was changed.

## Checkout and inputs

- Fresh clone: `/Users/kvallier/Desktop/TSE_Formal_chile`.
- Base: `bd80f4a5b94b691168533c7dd1a8df6e7f21f285` from `main`.
- Local branch: `chile-epistemic-evolution`.
- Toolchain: `leanprover/lean4:v4.28.0-rc1`.
- Mathlib: `5352afccd6866369be9de43f5b7ec47203555f44`.
- `lake exe cache get` completed successfully before builds; 7,873 cached files
  were unpacked. No specification code was executed.
- Both complete specifications, all four referee files, and the generating
  prompt were read across the implementation team before Lean edits. Input
  paths and SHA-256 hashes are in `EPIS_INPUTS_SHA256.json`.
- `origin/wip/jul29-modules` was read for reference; no merge or import from it.
- All 19 protected original kernel/configuration files are byte-identical to
  the base. `SEKernel.lean` and `AxiomsAudit.lean` were not modified.

## What compiled

| New module | Named theorems audited | Verified scope |
|---|---:|---|
| `SEKernel.FiniteProbability` | 46 | Finite laws/kernels, products, conditioning, total expectation, union/Markov/Chebyshev/Cantelli, separate-coordinate independence and iid mean/variance; exact Law1 aliases. |
| `SEKernel.FirstAppearancePlurality` | 54 | Total ordered plurality, abstention and N=0, relabelling, least maximal index, actual prefix reach, comparator cells, actual prefix consensus and probability partitions, overlap accounting, zero-mass appearance/winning. |
| `SEKernel.FirstTiedLabelCounting` | 13 | First T-labelled entry of a uniformly permuted fixed word has probability u_a/L; least-index semantics and count preservation. |
| `SEKernel.PluralityBounds` | 19 | Actual iid count geometric/rational tails, strict-correct and wrong-mode bounds, sole-label equality, common-gap cutoff. |
| `SEKernel.EpistemicPayoff` | 42 | Actual response-kernel three-cell accounting, accuracy/premium bridge, conditional-rate bounds, null-cell-safe weighted transfer error; hump/recognizer/advocate algebra with scope recorded in the ledger. |
| `SEKernel.PluralityConcentration` | 20 | Literal L/M/H reflection with sum_bij, layer cake, actual coupled probability/expectation balancing, zero-mass event restriction. |
| `SEKernel.EpistemicFinite` | — | Wave 1 umbrella importing these six finite modules; no optional analysis import. |
| `SEKernel.AxiomsAuditEpistemic` | 194 total | Every explicitly named new theorem, including all headlines. |

Cold verification removed the root project's generated `.lake/build` directory,
then rebuilt the umbrella; the fetched pinned Mathlib/package caches were kept.
This is a cold **project** build using the requested dependency cache.

- `lake build SEKernel.EpistemicFinite`: exit 0, 109.96 seconds.
- `lake build SEKernel.AxiomsAuditEpistemic`: exit 0, 48.76 seconds.

Full receipts: `EpistemicReports/Wave1/COLD_BUILD.log`, `AXIOMS_BUILD.log`,
`VERIFICATION.json`, `AUDIT_SUMMARY.json`, and source hashes in the summary.
The build has ordinary style/unused-hypothesis warnings; no errors remain.

## What remains unformalized

No requested source module is currently failing compilation. The following
**specification results remain unformalized**, rather than being represented by
placeholders, weaker statements, or hypotheses that assume their conclusion:

1. **IID multinomial count and overlap formulas.** The first-label permutation
   counting lemma is proved, but the IID conditional-count-to-shuffle bridge
   and `N!/∏c_a!` fiber enumeration are missing. Actual overlap event accounting
   is proved; the printed two-block multinomial joint formula is not.
2. **Weak-mode monotonicity and tied-mode completion.** The artificial-prior
   likelihood pairing, decision-value marginalization, and the increment
   `u^N(1-u)/M` are not installed. Tail bounds do not establish monotonicity.
3. **Sampling identities and numerical counterexamples.** The nonmodal
   examples, operational-Trap examples, size interactions, and distribution-level
   variety example have not been transported through a proved count formula.
   No symbolic polynomial substitution is claimed to be a probability proof.
4. **Full hump and prefix realizability.** Expanded/factored ten-call hump
   equality, endpoints, interior positivity, recognition thresholds, and the
   smaller peak inequality are proved algebraically. Their actual binary
   sampling identification, fair-tie bridge, general-k polynomial/derivative
   identities, ten-call union-bound specialization, and strengthened
   `k_keep=1 ⇒ k_post=1` prefix restriction remain unformalized.
5. **Full concentration/majorization.** The L/M/H coupling and layer cake are
   proved. Collapsed-word tie factorization, sorted-list HLP induction, and
   transport to voting/cell/premium majorization remain open. Any eventual
   premium theorem must use fixed parameter constants, not automatically the
   changing conditional means of one fixed kernel.
6. **Remaining model instantiations.** Several advocate/recognizer expressions
   are proved as supplied-stratum algebra; full conditional nomination and
   four-decider probability instantiations, response-kernel existence examples,
   and some task-weight/remainder corollaries are not yet installed.

`STATEMENTS_EPISTEMIC.md` maps each Wave 1 result to exact Lean names and status,
records every requested numerical example separately, and inventories later
wave results as not started. It also records the notation changes, N/k≥0
convention, explicit positivity requirements, and referee deviations.

## Axiom audit

All **194/194** named theorem audits passed. Exact distributions:

- 192: `[propext, Classical.choice, Quot.sound]`.
- 1 (`reaches_zero`): `[propext, Quot.sound]`.
- 1 (`postedWord_reaches_full`): no axioms.

No unexpected axiom occurs. A source scan found no custom axiom, sorry, admit,
native_decide, opaque declaration, user global instance, or decide call in the
new Lean files. The `deriving` declarations are ordinary kernel-checked finite
and equality instances. Classical mathematics was not hidden in constants.

The complete `#print axioms` output for every headline and every other named
new theorem is in `EpistemicReports/Wave1/AXIOMS.txt` and reproduced below.

```text
info: SEKernel/AxiomsAuditEpistemic.lean:4:0: 'SEKernel.FiniteProbability.Law.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:5:0: 'SEKernel.FiniteProbability.Law.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:6:0: 'SEKernel.FiniteProbability.Law.expect_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:7:0: 'SEKernel.FiniteProbability.Law.expect_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:8:0: 'SEKernel.FiniteProbability.Law.expect_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:9:0: 'SEKernel.FiniteProbability.Law.expect_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:10:0: 'SEKernel.FiniteProbability.Law.expect_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:11:0: 'SEKernel.FiniteProbability.Law.expect_centered' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:12:0: 'SEKernel.FiniteProbability.Law.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:13:0: 'SEKernel.FiniteProbability.Law.expect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:14:0: 'SEKernel.FiniteProbability.Law.prob_false' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:15:0: 'SEKernel.FiniteProbability.Law.prob_true' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:16:0: 'SEKernel.FiniteProbability.Law.prob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:17:0: 'SEKernel.FiniteProbability.Law.prob_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:18:0: 'SEKernel.FiniteProbability.Law.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:19:0: 'SEKernel.FiniteProbability.Law.prob_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:20:0: 'SEKernel.FiniteProbability.Law.prob_union_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:21:0: 'SEKernel.FiniteProbability.Law.prob_exists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:22:0: 'SEKernel.FiniteProbability.Law.expect_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:23:0: 'SEKernel.FiniteProbability.Law.mass_eq_zero_of_prob_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:24:0: 'SEKernel.FiniteProbability.Law.cellExpect_eq_zero_of_prob_eq_zero' depends on axioms: [propext,
info: SEKernel/AxiomsAuditEpistemic.lean:25:0: 'SEKernel.FiniteProbability.Law.prob_mul_conditionalMean' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:26:0: 'SEKernel.FiniteProbability.Law.total_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:27:0: 'SEKernel.FiniteProbability.Law.variance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:28:0: 'SEKernel.FiniteProbability.Law.variance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:29:0: 'SEKernel.FiniteProbability.Law.prob_le_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:30:0: 'SEKernel.FiniteProbability.Law.markov' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:31:0: 'SEKernel.FiniteProbability.Law.markov_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:32:0: 'SEKernel.FiniteProbability.Law.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:33:0: 'SEKernel.FiniteProbability.Law.shifted_square' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:34:0: 'SEKernel.FiniteProbability.Law.cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:35:0: 'SEKernel.FiniteProbability.Law.prod_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:36:0: 'SEKernel.FiniteProbability.Law.expect_pi_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:37:0: 'SEKernel.FiniteProbability.Law.expect_pi_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:38:0: 'SEKernel.FiniteProbability.Law.expect_pi_coord_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:39:0: 'SEKernel.FiniteProbability.Law.variance_sum_of_uncorrelated' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:40:0: 'SEKernel.FiniteProbability.Law.variance_pi_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:41:0: 'SEKernel.FiniteProbability.Law.variance_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:42:0: 'SEKernel.FiniteProbability.Law.iid_average' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:43:0: 'SEKernel.FiniteProbability.Law.expect_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:44:0: 'SEKernel.FiniteProbability.Law.expect_map' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:45:0: 'SEKernel.FiniteProbability.Law.expect_prod_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:46:0: 'SEKernel.FiniteProbability.Law.expect_prod_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:47:0: 'SEKernel.FiniteProbability.Law.expect_prod_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:48:0: 'SEKernel.FiniteProbability.Law.variance_prod_add' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:49:0: 'SEKernel.FiniteProbability.Kernel.comp_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:50:0: 'SEKernel.Epistemic.labelCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:51:0: 'SEKernel.Epistemic.labelCount_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:52:0: 'SEKernel.Epistemic.labelCount_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:53:0: 'SEKernel.Epistemic.candidatePositions_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:54:0: 'SEKernel.Epistemic.plurality_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:55:0: 'SEKernel.Epistemic.candidatePositions_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:56:0: 'SEKernel.Epistemic.plurality_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:57:0: 'SEKernel.Epistemic.plurality_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:58:0: 'SEKernel.Epistemic.plurality_mem_word' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:59:0: 'SEKernel.Epistemic.plurality_maximal_count' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:60:0: 'SEKernel.Epistemic.plurality_dominates_readable' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:61:0: 'SEKernel.Epistemic.plurality_first_maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:62:0: 'SEKernel.Epistemic.plurality_unique_readable' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:63:0: 'SEKernel.Epistemic.postedWord_reaches_full' does not depend on any axioms
info: SEKernel/AxiomsAuditEpistemic.lean:64:0: 'SEKernel.Epistemic.postedWord_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:65:0: 'SEKernel.Epistemic.comparatorCell_keep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:66:0: 'SEKernel.Epistemic.comparatorCell_posted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:67:0: 'SEKernel.Epistemic.comparatorCell_absent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:68:0: 'SEKernel.Epistemic.reaches_zero' depends on axioms: [propext, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:69:0: 'SEKernel.Epistemic.correctVote_reaches_full' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:70:0: 'SEKernel.Epistemic.correctVote_need_not_reach_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:71:0: 'SEKernel.Epistemic.labelCount_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:72:0: 'SEKernel.Epistemic.labelCount_disjoint_sum_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:73:0: 'SEKernel.Epistemic.consensus_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:74:0: 'SEKernel.Epistemic.falseConsensus_not_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:75:0: 'SEKernel.Epistemic.consensusCell_correct_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:76:0: 'SEKernel.Epistemic.consensusCell_wrongPosted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:77:0: 'SEKernel.Epistemic.consensusCell_wrongAbsent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:78:0: 'SEKernel.Epistemic.consensusCell_noConsensus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:79:0: 'SEKernel.Epistemic.consensusCellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:80:0: 'SEKernel.Epistemic.prefix_consensus_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:81:0: 'SEKernel.Epistemic.prefixConsensusCell_correct_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:82:0: 'SEKernel.Epistemic.prefixConsensusCell_wrongPosted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:83:0: 'SEKernel.Epistemic.prefixConsensusCell_wrongAbsent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:84:0: 'SEKernel.Epistemic.prefixConsensusCell_noConsensus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:85:0: 'SEKernel.Epistemic.prefixConsensusCellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:86:0: 'SEKernel.Epistemic.prefix_falseConsensus_probability_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:87:0: 'SEKernel.Epistemic.falseConsensus_probability_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:88:0: 'SEKernel.Epistemic.falseConsensus_probability_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:89:0: 'SEKernel.Epistemic.prob_pi_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:90:0: 'SEKernel.Epistemic.prob_single_label_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:91:0: 'SEKernel.Epistemic.no_appearance_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:92:0: 'SEKernel.Epistemic.reach_full_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:93:0: 'SEKernel.Epistemic.prefixPositions_card' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:94:0: 'SEKernel.Epistemic.reach_prefix_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:95:0: 'SEKernel.Epistemic.voteAccuracy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:96:0: 'SEKernel.Epistemic.voteAccuracy_le_reach_full' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:97:0: 'SEKernel.Epistemic.zero_mass_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:98:0: 'SEKernel.Epistemic.zero_mass_voteAccuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:99:0: 'SEKernel.Epistemic.cellProbability_total' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:100:0: 'SEKernel.Epistemic.cellProbability_keep' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:101:0: 'SEKernel.Epistemic.jointVote_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:102:0: 'SEKernel.Epistemic.cellProbability_posted' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:103:0: 'SEKernel.Epistemic.cellProbability_absent' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:104:0: 'SEKernel.Epistemic.uniformLaw_prob_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:105:0: 'SEKernel.Epistemic.firstActive_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:106:0: 'SEKernel.Epistemic.firstActive_min' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:107:0: 'SEKernel.Epistemic.firstActive_eq_of_min' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:108:0: 'SEKernel.Epistemic.swap_mem_active' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:109:0: 'SEKernel.Epistemic.firstActive_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:110:0: 'SEKernel.Epistemic.firstActive_atom_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:111:0: 'SEKernel.Epistemic.prob_mem_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:112:0: 'SEKernel.Epistemic.firstActive_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:113:0: 'SEKernel.Epistemic.firstActive_label_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:114:0: 'SEKernel.Epistemic.firstTLabel_semantics' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:115:0: 'SEKernel.Epistemic.firstTLabel_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:116:0: 'SEKernel.Epistemic.shuffledWord_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:117:0: 'SEKernel.Epistemic.geometric_mul_affine_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:118:0: 'SEKernel.Epistemic.geometric_le_rational' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:119:0: 'SEKernel.Epistemic.countTailCoefficient_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:120:0: 'SEKernel.Epistemic.countTilt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:121:0: 'SEKernel.Epistemic.countTilt_product' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:122:0: 'SEKernel.Epistemic.countTilt_one_le_of_count_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:123:0: 'SEKernel.Epistemic.expect_countTilt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:124:0: 'SEKernel.Epistemic.rational_tilt_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:125:0: 'SEKernel.Epistemic.iid_count_geometric_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:126:0: 'SEKernel.Epistemic.iid_count_rational_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:127:0: 'SEKernel.Epistemic.readable_winner_dominates' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:128:0: 'SEKernel.Epistemic.wrong_mode_geometric_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:129:0: 'SEKernel.Epistemic.wrong_mode_rational_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:130:0: 'SEKernel.Epistemic.failed_vote_count_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:131:0: 'SEKernel.Epistemic.correct_mode_geometric_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:132:0: 'SEKernel.Epistemic.correct_mode_rational_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:133:0: 'SEKernel.Epistemic.sole_readable_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:134:0: 'SEKernel.Epistemic.correct_mode_common_rational_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:135:0: 'SEKernel.Epistemic.correct_mode_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:136:0: 'SEKernel.EpistemicPayoff.correctness_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:137:0: 'SEKernel.EpistemicPayoff.cellOf_keep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:138:0: 'SEKernel.EpistemicPayoff.sum_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:139:0: 'SEKernel.EpistemicPayoff.CellModel.weight_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:140:0: 'SEKernel.EpistemicPayoff.premium_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:141:0: 'SEKernel.EpistemicPayoff.premium_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:142:0: 'SEKernel.EpistemicPayoff.premium_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:143:0: 'SEKernel.EpistemicPayoff.premium_le_post_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:144:0: 'SEKernel.EpistemicPayoff.premium_transfer_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:145:0: 'SEKernel.EpistemicPayoff.premium_transfer_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:146:0: 'SEKernel.EpistemicPayoff.premium_transfer_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:147:0: 'SEKernel.EpistemicPayoff.premium_coarse_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:148:0: 'SEKernel.EpistemicPayoff.responseMass_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:149:0: 'SEKernel.EpistemicPayoff.conditionalRate_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:150:0: 'SEKernel.EpistemicPayoff.mass_mul_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:151:0: 'SEKernel.EpistemicPayoff.partition_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:152:0: 'SEKernel.EpistemicPayoff.CellModel.ofLaw_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:153:0: 'SEKernel.EpistemicPayoff.responseRates_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:154:0: 'SEKernel.EpistemicPayoff.comparatorModel_keep' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:155:0: 'SEKernel.EpistemicPayoff.response_conditional_cell_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:156:0: 'SEKernel.EpistemicPayoff.response_accuracy_eq_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:157:0: 'SEKernel.EpistemicPayoff.response_premium_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:158:0: 'SEKernel.EpistemicPayoff.response_premium_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:159:0: 'SEKernel.EpistemicPayoff.response_premium_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:160:0: 'SEKernel.EpistemicPayoff.ordered_response_premium_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:161:0: 'SEKernel.EpistemicPayoff.hump_forms_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:162:0: 'SEKernel.EpistemicPayoff.hump_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:163:0: 'SEKernel.EpistemicPayoff.hump_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:164:0: 'SEKernel.EpistemicPayoff.hump_reach_vote_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:165:0: 'SEKernel.EpistemicPayoff.mixed_recognizer_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:166:0: 'SEKernel.EpistemicPayoff.mixed_recognizer_two' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:167:0: 'SEKernel.EpistemicPayoff.recognizer_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:168:0: 'SEKernel.EpistemicPayoff.small_hump_peak' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:169:0: 'SEKernel.EpistemicPayoff.advocate_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:170:0: 'SEKernel.EpistemicPayoff.advocate_rescue_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:171:0: 'SEKernel.EpistemicPayoff.nomination_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:172:0: 'SEKernel.EpistemicPayoff.nomination_same_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:173:0: 'SEKernel.EpistemicPayoff.coupled_nomination_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:174:0: 'SEKernel.EpistemicPayoff.advocate_break_even' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:175:0: 'SEKernel.EpistemicPayoff.four_decider_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:176:0: 'SEKernel.EpistemicPayoff.correlated_uptake_differs' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:177:0: 'SEKernel.EpistemicPayoff.absent_rescue_ceiling_counterexample' depends on axioms: [propext,
info: SEKernel/AxiomsAuditEpistemic.lean:178:0: 'SEKernel.EpistemicConcentration.symbolCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:179:0: 'SEKernel.EpistemicConcentration.symbolCount_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:180:0: 'SEKernel.EpistemicConcentration.reflect_involutive' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:181:0: 'SEKernel.EpistemicConcentration.symbolCount_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:182:0: 'SEKernel.EpistemicConcentration.symbolCount_reflect_low' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:183:0: 'SEKernel.EpistemicConcentration.symbolCount_reflect_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:184:0: 'SEKernel.EpistemicConcentration.symbolCount_reflect_high' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:185:0: 'SEKernel.EpistemicConcentration.wordMass_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:186:0: 'SEKernel.EpistemicConcentration.wordMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:187:0: 'SEKernel.EpistemicConcentration.power_swap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:188:0: 'SEKernel.EpistemicConcentration.wordMass_reflect_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:189:0: 'SEKernel.EpistemicConcentration.loss_count_order' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:190:0: 'SEKernel.EpistemicConcentration.reflect_loss_iff_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:191:0: 'SEKernel.EpistemicConcentration.central_word_mass_balancing' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:192:0: 'SEKernel.EpistemicConcentration.symmetric_layer_cake' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:193:0: 'SEKernel.EpistemicConcentration.symmetric_word_mass_balancing' depends on axioms: [propext,
info: SEKernel/AxiomsAuditEpistemic.lean:194:0: 'SEKernel.EpistemicConcentration.central_probability_balancing' depends on axioms: [propext,
info: SEKernel/AxiomsAuditEpistemic.lean:195:0: 'SEKernel.EpistemicConcentration.symmetric_expectation_balancing' depends on axioms: [propext,
info: SEKernel/AxiomsAuditEpistemic.lean:196:0: 'SEKernel.EpistemicConcentration.zero_label_word_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SEKernel/AxiomsAuditEpistemic.lean:197:0: 'SEKernel.EpistemicConcentration.zero_label_event_restriction' depends on axioms: [propext,
```

Stop at this Wave 1 checkpoint. No Wave 2/3 or public change is implied.
