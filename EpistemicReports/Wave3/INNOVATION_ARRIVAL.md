# Wave 3: InnovationArrival

`SEKernel.InnovationArrival` compiles. All 15 named theorems are audited; the
exact output is [INNOVATION_ARRIVAL_AXIOMS.txt](INNOVATION_ARRIVAL_AXIOMS.txt),
with [names/hash manifest](INNOVATION_ARRIVAL_THEOREMS.json) and
[audit receipt](INNOVATION_ARRIVAL_VERIFICATION.json). Final named-module build
log: `scratch/wave3/arrival_build_04.log`. Root performs combined verification.

## Source mapping

Every Lean name has prefix `SEKernel.InnovationArrival.`.

| Source | Lean theorem | Status and exact scope |
|---|---|---|
| A B7.2 / B E6a independent mutation arrival | `independent_no_appearance`, `independent_appearance` | Proved for the actual `mutationTrials` law: separate Bernoulli coordinates indexed by Fin(M*T). No appearance is the event that all coordinates are false. Includes M=0,T=0,u=0,u=1. |
| A B7.2 / B E6a exact conditional hazard given preceding absence | `absence_eq_of_conditional` | Proved for arbitrary finite history law and occurrence events; requires conditional creation probability u on every positive preceding-absence cell. Independence is unnecessary for this version. |
| B E6 lower-bound conditional creation probability | `absence_le_of_conditional_lower` | Proved: absence probability <=(1-u)^n, hence appearance >=1-(1-u)^n. The event prefix records absence in every preceding trial. Instantiate n=M*T. |
| B E6 upper-bound conditional creation probability | `absence_ge_of_conditional_upper` | Proved: absence probability >=(1-u)^n, hence appearance <=1-(1-u)^n. The upper bound is conditional given absence, not an unsupported marginal assumption. |
| B E6b union/Bernoulli bound | `one_sub_pow_le_mul`, `appearance_le_trials_mul`, `independent_appearance_le` | Proved: appearance <=(M*T)*u under the conditional upper bound, and for the actual IID law. |
| A B7 appearance is not establishment | `presence_le_appearance` | Proved under explicit containment of the present-at-horizon event in the earlier-appearance event. No retention or fixation claim is assumed. |
| B E6 zero support under mutation-free selection | `selection_zero`, `selectionIter_zero` | Proved for the existing Law1.step and its finite iteration. No mutation/crossover/immigration is part of this operator. |
| Finite hazard accounting ingredients | `avoids_zero`, `avoids_succ`, `absence_partition`, `first_creation_mass` | Proved; the last identity converts positive-cell conditional means to actual first-arrival mass. Null cells are handled without arbitrary conditional assertions. |

Parameter bounds are 0<=u<=1. Trial prefixes and generations start at zero.
The finite product uses M*T trial coordinates; grouping them into T generations
of M offspring changes no stated event or probability. The probability of
current presence requires the separate event containment above.

## Remaining scope

The complete replay matrix-power formula A B7.1 is not formalized by this module.
It requires a full specified score/history/retention metadata transition; Wave 3
requests the arrival results, not a simulator completion. Actual arrival does
not prove selective establishment or F15's empirical replay-error factor.
No analytic waiting-time limits are introduced.
