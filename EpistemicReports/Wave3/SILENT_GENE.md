# Wave 3 lane: SilentGene

`SEKernel.SilentGene` compiles (exit 0). The source is frozen after the successful
final lane build. All **47 named theorems** print exactly
`[propext, Classical.choice, Quot.sound]`. The comment-stripped scan found no
forbidden constructs. No existing module was edited; no Git mutation occurred.
Root performs the protected-file and combined umbrella verification.

Receipts: [build](SILENT_GENE_BUILD.log), [exact axioms](SILENT_GENE_AXIOMS.txt),
[all theorem names and source hash](SILENT_GENE_THEOREMS.json),
[verification summary](SILENT_GENE_VERIFICATION.json).

## Representation and faithful model boundary

Genotypes are `Bool × Bool`: the first bit is board and the second advocate.
`fitness v b c` gives both voters fitness `v`, plain boards `b`, and advocate
boards `c`. The parameter `c` is the specification's `b+a`; allowing any positive
`c` includes negative advocate advantage. The clonal results require positive
`v,b,c`; the crossing model additionally requires `v<b<c` and positive initial
compartment masses. All generation indices start at zero.

`clonalTrajectory` is normalized from the **actual finite Law mass**, and
`clonalTrajectory_step` proves it follows the existing `Law1.step`. These results
are not about noisy truncation selection or realized finite offspring counts.
Conditional frequencies retain explicit positive compartment hypotheses.

`CrossingModel` permits unnormalized initial masses `r,u,h`, since multiplying
all three by a common positive number leaves the threshold tests invariant.
`board_half_frequency_iff` and `advocate_half_frequency_iff` prove the tests for
actual normalized four-genotype trajectories. Crossing existence is proved from
finite Bernoulli inequalities and the Archimedean property, never assumed.

## Specification-to-Lean map

All names below have prefix `SEKernel.SilentGene.` unless otherwise indicated.

| Source result | Lean names | Status / hypotheses |
|---|---|---|
| A C0 / B C.1: positive four-genotype constant fitness | `fitness`, `fitness_pos`, `clonal_mean` | Proved; `c` is the free positive resulting fitness `b+a` |
| A C1 / B C1b: voter conditional silence `z'=z` | `silent_frequency_preserved` | Proved under positive fitness and positive voter mass |
| A C1 / B C1b: exact conditional advocate update independent of total board share | `advocate_frequency_step` | Proved for actual Law1.step, written as `c*x11/(b*x10+c*x11)`; positive board mass |
| A C1 / B C1c: advocate odds multiply by `c/b` | `advocate_odds_step` | Proved for the actual board-coordinate ratio; positive plain-board mass |
| A C1 / B C2a: exact finite clonal solution | `clonalTrajectory_zero`, `clonalTrajectory_nonneg`, `clonalTrajectory_total`, `clonalTrajectory_mean`, `clonalTrajectory_step`, `constant_fitness_closed_form` | Proved for every finite type, finite Law, and positive constant fitness |
| A C1 / B C2a: specialized normalizer `r*v^t+u*b^t+h*c^t` | `four_genotype_normalizer` | Proved |
| A C1 / B C2b: finite board/advocate conditional formulas | `board_frequency_time`, `advocate_frequency_time`, `silent_frequency_time`, `advocate_odds_time` | Proved; explicit positivity for conditional compartments |
| A C1: finite advocate and board deficit bounds | `complement_fraction_bound`, `advocate_deficit_bound`, `board_deficit_bound` | Proved; positive advocate initial mass for advocate bound, positive board mass and `b≤c` for board bound; strict ratios below one are additional ordered-fitness consequences |
| A C3 / B C2c–d: half-frequency tests | `board_half_frequency_iff`, `advocate_half_frequency_iff` | Proved for actual clonal trajectories, exactly the ratio-power tests |
| A C3 / B C2f–g: finite Bernoulli crossing certificates | `CrossingModel.advocate_bernoulli_certificate`, `.board_bernoulli_certificate`, `.linear_certificate_exists`, `.advocate_exists`, `.board_exists`, `.advocateTime_le_bernoulli`, `.boardTime_le_bernoulli` | Proved; all existence assumptions discharged using `one_add_mul_le_pow` |
| A C3 / B C2e: first crossing times and exact ordering criterion | `CrossingModel.advocateTime`, `.boardTime`, `.advocateTime_spec`, `.boardTime_spec`, `.advocateTime_le`, `.boardTime_le`, `.board_before_advocate_iff` | Proved; both times use Nat.find; criterion retains `1≤advocateTime` guard |
| A C3 / B C.2: threshold verification from crossing and preceding failure | `CrossingModel.boardTime_eq_of_predecessor`, `.advocateTime_eq_of_predecessor` | Proved; both mass sequences monotone |
| A C3: crossing pair `(4,1)` | `advocateFirstA_crossings` | Counterexample to forced board-first ordering; exact rational power comparisons through the proved crossing certificates and norm_num |
| A C3 and B C.2: crossing pair `(2,6)` | `boardFirst_crossings` | Proved opposite order; exact rational power comparisons through the proved crossing certificates and norm_num |
| B C.2: crossing pair `(3,2)` | `advocateFirstB_crossings` | Counterexample to forced board-first ordering; exact rational power comparisons through the proved crossing certificates and norm_num |
| A C4 / B C.5: removing voters need not lower conditional silent frequency | `removing_voters_does_not_suppress_silent` | Actual-law counterexample: voter share falls from `1/2` to `2/7`, silent frequency remains `1/2` |

The remaining named theorems in the 47-theorem manifest are the ordered-fitness
and monotonicity ingredients: `CrossingModel.b_pos`, `.c_pos`, `.bv_gt_one`,
`.cv_gt_one`, `.cb_gt_one`, `.boardMass_monotone`, `.advocateMass_monotone`.

## Explicit omissions and ownership boundaries

- B C.1's separate scalar-`y` expression `c*y/(b*(1-y)+c*y)`, its strict sign
  equivalence, and endpoint preservation were not installed as separately named
  theorems. The delivered actual-coordinate conditional formula and odds identity
  are proved, but the additional scalar presentation/sign/endpoints are absent.
  The lane was bounded at the core clonal and crossing results.
- No analytic limits, logarithms, or ceiling formula for crossing times are
  formalized; these are unnecessary for the finite certificate targets.
- Crossover, mutation, elite retention, the one-step low silent levels, and
  finite-population expected ratios belong to `GenotypeTransition`, not this lane.
  This report does not claim those results from clonal selection alone.
- The whole all-individual selection/recombination/mutation countermodel in A C4
  is not formalized by this module. It requires the separate lifecycle operators
  and an induction preserving the conditional order; the delivered actual clonal
  counterexample is a distinct specified refutation, not a weakened replacement.
