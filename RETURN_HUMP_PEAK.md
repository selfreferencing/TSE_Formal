# Hump peak and worst-case voting return — 2026-10-21

All requested statements A1-A5, B1 and B2 are proved in two new modules,
using the existing `hump10`, `Law`, `reachProbability` and `voteAccuracy`.
No existing theorem statement was changed.

## Mathematical statements and Lean names

Names in this first table have namespace `SEKernel.Closeout.HumpPeak`.
Write `h = hump10` and `r = humpPeak`.

| Target | Plain mathematical statement | Lean name |
| --- | --- | --- |
| A1 | For every real p, h is differentiable at p with derivative (1-p)^4(5-630p^4). | `hump10_hasDerivAt` |
| A2 | r = sqrt(sqrt(1/126)), r > 0, and r^4 = 1/126. | `humpPeak`, `humpPeak_pos`, `humpPeak_pow_four` |
| A2 | 29/100 < r < 3/10. | `humpPeak_bounds` |
| A3 | h is strictly increasing on [0,r]. | `hump10_strictMonoOn` |
| A3 | h is strictly decreasing on [r,1]. | `hump10_strictAntiOn` |
| A4 | For every p in [0,1], h(p) <= h(r). | `hump10_le_peak` |
| A4 | For every p in [0,1], h(p) = h(r) if and only if p = r. | `hump10_eq_peak_iff` |
| A5 | 7331/10000 < h(r) < 7332/10000. | `hump10_peak_value` |

The additional theorem `humpPeak_tight_bounds` proves the exact rational
enclosure 2984745/10000000 < r < 2984747/10000000. This enclosure and
the existing factored polynomial certify A5 by rational arithmetic.
The derivative is proved from the existing factored form by derivative rules
and a ring identity; strict monotonicity follows from the mean value theorem.

Names in the next table have namespace `SEKernel.Closeout.HumpWorstCase`.
Here A is any finite answer type with decidable equality, a is the right
answer, pi is its actual law on Option A, and p = pi.mass (some a).

| Target | Plain mathematical statement | Lean name |
| --- | --- | --- |
| B1 | If pi.mass none = 0, then reachProbability(pi,10,5,a) - voteAccuracy(pi,10,a) <= h(p). | `premium_le_hump10` |
| B2 | Under the same hypothesis, if at most one wrong label has positive mass, then that premium equals h(p). | `premium_eq_hump10_of_single_wrong` |

The B2 hypothesis is spelled out as: for any b,c different from a, if
pi.mass(some b) > 0 and pi.mass(some c) > 0, then b = c.
This includes the case where no wrong label has positive mass.

## Supporting constructions

The B proof uses a direct ordered-word coupling instead of the suggested
majorization route. The definition `mergeWrong` fixes abstention, sends a to true, and
sends every wrong label to false. The existing IID pushforward theorem
identifies its actual binary law, and `binary_hump_identification` supplies
the premium identity. This changes the proof route, not either statement.

| Lean name in `SEKernel.Closeout.HumpWorstCase` | Plain mathematical content |
| --- | --- |
| `labelCount_map_le` | Merging labels cannot lower the count of the image of any label. |
| `plurality_of_map_correct` | If a label map preserves abstention and the exact right-answer positions, a right win after merging implies a right win before merging, with the original first-appearance ties. |
| `mergeWrong_none` | The preimage of abstention under mergeWrong is exactly abstention. |
| `mergeWrong_correct` | The preimage of true under mergeWrong is exactly the right answer. |
| `mergeWrong_mass_none` | The merged law has the same abstention mass. |
| `mergeWrong_mass_correct` | The merged law has the same right-answer mass. |
| `mergeWrong_voteAccuracy_le` | For every sample size, merging wrong answers weakly lowers voting accuracy, also allowing abstention. |
| `plurality_map_on_word` | A map injective on the labels present in one word preserves that word's plurality winner. |
| `mergeWrong_voteAccuracy_eq` | With at most one positive-mass wrong label, merging preserves voting accuracy at every sample size. |

B2 applies the last two facts only to words with nonzero probability.
Every other word contributes zero to the actual finite probability sum.
Thus no unsupported restriction on all possible words is assumed.

Statement-form choices: A4's upper bound and equality characterization are
separate theorems for reuse. A2 uses nested square roots, as permitted,
and proves the requested positive-root equation. No assertion was weakened.

## Verification

| Command | Exit code |
| --- | --- |
| `lake env lean SEKernel/CloseoutHumpPeak.lean` | 0 |
| `lake env lean SEKernel/CloseoutHumpWorstCase.lean` | 0 |
| `lake build SEKernel.EpistemicFinite` | 0 (7,917 jobs) |
| `lake env lean SEKernel/AxiomsAuditEpistemic.lean` | 0 |

Integration appends two imports to `SEKernel/EpistemicFinite.lean` and one
`#print axioms` line for each of the 21 new theorems to
`SEKernel/AxiomsAuditEpistemic.lean`. Both earlier files retain their complete
original contents as byte-for-byte prefixes. The toolchain, lakefile and
manifest are unchanged; no dependency update was run.

All 21 new theorems use only the permitted axioms: 19 use
`[propext, Classical.choice, Quot.sound]`; 2 use `[propext]`.
The complete audit covers 1,099 theorems, with no nonstandard axiom,
`sorryAx` or `ofReduceBool`. Both new sources pass the comment-stripped
forbidden-token scan, including no `sorry`, `admit`, custom `axiom`,
`native_decide`, `opaque`, `unsafe`, `implemented_by`, `run_tac`, `elab`,
or `decide`. No existing mathematics source was edited.

Exact new-theorem output from the combined audit:

```text
'SEKernel.Closeout.HumpPeak.hump10_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.humpPeak_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.humpPeak_pow_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.humpPeak_tight_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.humpPeak_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.hump10_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.hump10_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.hump10_le_peak' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.hump10_eq_peak_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpPeak.hump10_peak_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.labelCount_map_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.plurality_of_map_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.mergeWrong_none' depends on axioms: [propext]
'SEKernel.Closeout.HumpWorstCase.mergeWrong_correct' depends on axioms: [propext]
'SEKernel.Closeout.HumpWorstCase.mergeWrong_mass_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.mergeWrong_mass_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.mergeWrong_voteAccuracy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.premium_le_hump10' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.plurality_map_on_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.mergeWrong_voteAccuracy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SEKernel.Closeout.HumpWorstCase.premium_eq_hump10_of_single_wrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Local Git scope

Base: `8045f4565adcd7e918a15b5e0fd682675d389a1f`, the current
`chile-epistemic-evolution` tip at the start of this task.
Work is confined to the new local branch `chile-hump-peak`.
Only the two new mathematics modules, the two append-only integration files,
this return, and `STATEMENTS_EPISTEMIC.md` are included in the commit.
No other branch is changed. Nothing is pushed and no pull request is opened.
