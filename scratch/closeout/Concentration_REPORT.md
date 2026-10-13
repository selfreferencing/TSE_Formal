# Close-out: Concentration (Doc B A6.2–A6.5) — report

File: `SEKernel/CloseoutConcentration.lean` (1,765 lines), namespace `SEKernel.Closeout.Concentration`.
Imports: `SEKernel.PluralityConcentration`, `SEKernel.EpistemicPayoff`, `SEKernel.PluralityCountFormula` (all with oleans; no other Closeout file imported). No other file touched; no git writes.

All four targets are **proved**. Nothing remains open.

| Target | Lean theorem name(s) | Statement gist | Status |
|---|---|---|---|
| 1. One balancing transfer (A6.2) | `balancing_transfer_cells` (main), `balancing_transfer_win`, `concentrating_transfer_cells`, `balancing_transfer_premium` | Laws `π, π'` on `Option A`; correct `a`; wrong `i ≠ j` (both ≠ `a`); `π' = π` off `{some i, some j}` (so `p`, `u`, the other wrong labels are fixed); same pair sum; `\|π'ᵢ−π'ⱼ\| ≤ \|πᵢ−πⱼ\|`. Then for **every** `N, k`: `V_N`, `P(V∧R_k)`, `P(V∧R_kᶜ)` weakly rise, and `cellProbability … .posted` and `.absent` (wrong vote with correct posted / not posted) weakly fall. `concentrating_transfer_cells` is Doc B's direction: `q_j ≤ q_i`, `τ ≥ 0`, `(q_i,q_j) → (q_i+τ, q_j−τ)` lowers `V_N` and raises both wrong-vote cells. `balancing_transfer_premium`: same for `premium κ`. | proved |
| 1a. route lemmas | `wordSum_collapse`, `sum_collapse_fiber`, `decodeWord_not`, `fiberAverage_symm`, `fiberAverage_mono`, `bool_balancing`, `binomial_balance_fin`, `plurality_of_dominated`, `decode_win_conditions` | Collapse `j` onto `i` (wildcard). Each IID word sum factors as collapsed-word weight × `∏ m(j)^#j m(i)^#i` over the wildcard labellings (explicit bijection). The win indicator, averaged over each count fiber, is symmetric (`i↔j` swap = complement, via `plurality_relabel`), zero when a wild side exceeds the correct count, and maximal when both sides are below it (`plurality_of_dominated`). So the average is symmetric and nondecreasing toward the centre. The existing `symmetric_word_mass_balancing` then applies after an L/M/H→Bool marginalisation (`fin3_marginal`). Zero masses, `s = 0` and `x+y = 0` are all handled. | proved |
| 2. HLP reduction (A6.3) | `hlp_majorizes`, `hlp_sorted` | `Majorizes x y` (x more concentrated) := ∃ enumerations `σ τ : Fin (card W) ≃ W` with `x∘σ`, `y∘τ` antitone, prefix sums of `y∘τ` ≤ those of `x∘σ` for every `r`, and equal totals. Then `ReflTransGen BalancingStep x y`. A `BalancingStep` is a two-coordinate move: same sum, weakly smaller absolute difference (a swap is the equality case). Proof: Robin-Hood/T-transform induction on the number of disagreeing sorted coordinates. Permutations are products of swaps (`perm_reaches`). Zeros and ties need no hypotheses. | proved |
| 3. Concentration theorem (A6.4) | `concentration_cells`, `concentration_premium`, `concentration_win`, `premium_eq` | Same `π(none)` and `π(some a)`, and `Majorizes (wrongMass π a) (wrongMass π' a)`. Then `V_N(π) ≤ V_N(π')`, `pPost(π) ≥ pPost(π')`, `pNone(π) ≥ pNone(π')`, and for **fixed parameters** `κ` with `∀ c, 0 ≤ κ c ≤ 1`: `premium κ π' N k a ≤ premium κ π N k a`. `premium` is `EpistemicPayoff.comparatorModel(...).premium κ`, and `premium_eq` gives `κ_post·pPost + κ_none·pNone − (1−κ_keep)·V_N`. κ is never a conditional mean. | proved |
| 4. Size counterexample (A6.5) | `size_interaction_counterexample`, `vote_conc_4/5`, `vote_diff_4/5`, `voteAccuracy_law3`, `conc_majorizes_diff`, `conc_premium_ge_diff` | Actual IID laws on `Option (Fin 3)`: `p = 3/4`, no abstention, `k = N`, `κ = (keep 1, post 1, none 0)`. Concentrated `(1/4, 0)`: `D₄ = 39/256`, `D₅ = 105/1024`. Diffuse `(1/8, 1/8)`: `D₄ = 51/512`, `D₅ = 285/4096`. Concentrated is strictly higher at each size, but `(D₅−D₄)_conc − (D₅−D₄)_diff = −81/4096`. Values come from `plurality_multinomial_formula` (reduced to nested antidiagonals) by `simp`/`norm_num`; no `native_decide`. `conc_majorizes_diff` proves `(1/4,0)` majorizes `(1/8,1/8)`, so `concentration_premium` applies at every size. | proved |

## Compile
`lake env lean SEKernel/CloseoutConcentration.lean` → **exit 0**, 0 errors, 16 warnings. All warnings are linter-only (unused auto-included section variables; two `<;>` style hints).

## Axiom check (`scratch/closeout/concentration/AxCheck.lean`, exit 0)
All 26 checked headlines print `depends on axioms: [propext, Classical.choice, Quot.sound]`:
binomial_balance_fin, bool_balancing, plurality_of_dominated, wordSum_collapse, wordSum_balancing, decode_win_conditions, wordSum_win_balancing, balancing_transfer_win, balancing_transfer_cells, concentrating_transfer_cells, balancing_transfer_premium, hlp_sorted, hlp_majorizes, concentration_win, concentration_cells, concentration_premium, premium_eq, voteAccuracy_law3, vote_conc_4, vote_conc_5, vote_diff_4, vote_diff_5, premium_full_post, size_interaction_counterexample, conc_majorizes_diff, conc_premium_ge_diff.

No `sorry`/`admit`/`native_decide`/`axiom`/`opaque`/`implemented_by`/`extern`/`unsafe`/`instance`/`maxHeartbeats` appear in the file. The word `decide` appears only as the Bool-valued function `Decidable.decide` inside terms (for labellings), never as a tactic.

## Notes for the referee
- `Majorizes` takes the sorted rearrangements as explicit enumerations (∃ σ τ). Sorted rearrangements are unique, so this matches Doc B's definition. As a hypothesis, the ∃ form is the weakest reading.
- `ReadsOnly a E` (the event depends only on the positions of `a`) covers `True`, `R_k` and `R_kᶜ`. The transfer and concentration theorems are proved for `P(V ∧ E)` with any such `E`.
- Reach invariance is proved for every `k`, including `k > N` (`reachProbability_eq_min`).
