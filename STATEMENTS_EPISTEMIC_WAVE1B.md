# Wave 1b statement ledger

Current through the Wave 1b checkpoint. This addendum supersedes the corresponding
“not formalized” entries in the historical Wave 1 ledger; it does not close all Part A.
Statuses and explicit hypotheses are given theorem by theorem in the two adopted
lane mappings below. A nearby ingredient is never counted as its missing consumer.

- [Count-law keystone: exact statements, hypotheses, names](EpistemicReports/Wave1b/COUNT_LAW.md)
- [Plurality formula, consensus and numerical witnesses](EpistemicReports/Wave1b/COUNT_CONSUMERS.md)
- [All 52 audited theorem names](EpistemicReports/Wave1b/THEOREMS.json)
- [Exact per-theorem axiom output](EpistemicReports/Wave1b/AXIOMS.txt)

## Current coverage and deviations

Doc B A3.1's multinomial probability and plurality formula are proved for the actual
IID law. The binary count law and conditional uniform shuffle are proved. The
first active tied-label probability and fixed-count first-coordinate j/N ingredient
are proved. Doc B A4.4/A4.7's five-draw wrong-consensus polynomial and all three
operational-Trap/mode witnesses are proved for actual finite laws.

We use N and prefix indices starting at zero, with positivity assumptions stated
where needed. `readableModes` excludes zero readable maxima: its empty set on the
all-abstention profile has the same zero success weight as the specifications.
Conditional count ratios explicitly require positive cell probability; the
unnormalized shuffle bridge has no such restriction. The multinomial coefficient
is both a proved natural coefficient and a proved real factorial ratio.

The actual plurality formula does not assert uniform tie weights after conditioning
on a posted prefix. The count-law ingredient does not by itself prove binary
voter-count cancellation. Numerical probabilities are derived from proved finite
count formulas and then evaluated with norm_num.

## Not formalized at this checkpoint

| Result | Reason / missing object |
|---|---|
| Overlapping 10/5 two-block joint count law; prefix-conditional tie weights | Concatenation/product-law and prefix-event transport remain unconstructed. The marginal formula is proved. |
| Fair ties V_(2k)=V_(2k-1) | j/N fairness and the binomial law are proved; the required finite-sum cancellation is not. |
| Actual binary 10/5 ideal-recognizer premium equals hump10 | Needs the missing overlap/prefix counting adapter. Existing hump polynomial algebra is not promoted to a sampling result. |
| Binary prefix realizability: keep=1 implies post=1 | Actual prefix-event implication/probability argument remains unproved. |
| General-k hump and derivative identities; imperfect-recognizer sampling instantiations | No additional general-k polynomial or sampling adapter was installed; retain the precisely scoped Wave 1 algebra. |
| Specialized union bound 1-V <= 10(1-p) | Generic finite union bound exists; the ten-coordinate event containment and specialization were not installed. |
| Doc B A3.4 weak-mode quantitative voter monotonicity | The artificial-relabelling-prior/word-sum proof remains unformalized. No monotonicity premise substitutes for it. |
| Nonmodal examples (3/8,1/8,1/2), (2/5,1/2,1/10) at specified sizes | Full actual plurality formula is proved; small count-profile enumeration and evaluations remain unfinished. |
| Both size-interaction witnesses and distribution-level variety witness | Required exact probability consumers remain unformalized. |
| Collapsed-word factorization, sorted-list HLP, full concentration transport and fixed-constant premium theorem | No complete word-collapse/majorization transport was installed. Wave 1 local swap and algebraic results retain their original limited scope. |
| Remaining actual advocate/nomination/recognizer adapters | The Wave 1 algebra and explicit aggregate-hypothesis ceiling remain as previously scoped; no new stochastic identification is claimed. |

Other unmodified Part A entries retain their statuses in
[the historical Wave 1 ledger](STATEMENTS_EPISTEMIC_WAVE1.md).
