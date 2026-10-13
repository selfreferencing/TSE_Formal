# Close-out report: Doc B Theorem A3.4 (finite monotonicity for a correct mode)

Date: Tue Oct 13 01:12 EDT 2026 (from `date`).
File: `SEKernel/CloseoutModalMonotonicity.lean` (470 lines, namespace
`SEKernel.Closeout.ModalMonotonicity`, imports `SEKernel.PluralityBounds` only).
sha256 644ec4a4dc4e49931ddc766529982b9826a33c8cc07dfb38099434fa4795114a.

## Status: COMPLETE. The full theorem is proved; nothing remains open.

Compile: `lake env lean SEKernel/CloseoutModalMonotonicity.lean` gives exit 0
with no errors and no warnings (log: `scratch/closeout/modal/final.log`, empty).
No other file was modified. No git write commands were run. `lake build` was
never run.

## Headline (exact statement)

```lean
theorem voteAccuracy_succ_sub_ge {A : Type*} [Fintype A]
    (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some c) ≥ π.mass (some b)) (N : ℕ) :
    voteAccuracy π (N + 1) c - voteAccuracy π N c ≥
      π.mass none ^ N * (1 - π.mass none) / (Fintype.card A : ℝ)
```

`voteAccuracy` is the existing definition in `FirstAppearancePlurality.lean`.
There is no `DecidableEq A` assumption; the proof uses `classical`. A is
nonempty because `c : A` is given, so no separate `Nonempty` hypothesis is
needed. The mode hypothesis is weak, so ties are allowed.

## Corollaries

- `modalIncrement_nonneg`: `0 ≤ u^N (1-u) / M`.
- `voteAccuracy_le_succ`: `voteAccuracy π N c ≤ voteAccuracy π (N+1) c`.
- `voteAccuracy_monotone`: `Monotone (fun N => voteAccuracy π N c)`.
- Sharpness, `voteAccuracy_succ_sub_eq_of_subsingleton` (`[Subsingleton A]`):
  the bound holds with equality, `V_{N+1} - V_N = u^N (1-u) / M`.

## Main lemmas (the Doc B proof route, step by step)

The weights are unnormalized and indexed by `ρ = σ⁻¹`:
`stateLikelihood π ρ z = ∏ i, π.mass (optionCongr ρ (z i))` and
`jointWeight π c z d = ∑ ρ : Perm A, if ρ d = c then stateLikelihood π ρ z else 0`.
This equals `M!` times Doc B's `W_N(z,d)`.
`winnerOr c z = (plurality z).getD c`.
`fixCount c = #{ρ | ρ c = c}`, as a real number, which is `(M-1)!`.

1. Swap pairing.
   - `prod_pow_le_prod_pow_swap`: the exchange factor `(pq)^b(p^{a-b}-q^{a-b}) ≥ 0`.
   - `prod_word_le_prod_word_swap`: the same inequality in word form.
   - `jointWeight_le_of_labelCount_le`: if `hmode` holds and
     `labelCount z (some d) ≤ labelCount z (some e)`, then
     `jointWeight π c z d ≤ jointWeight π c z e`. The bijection is
     `ρ ↦ ρ * swap d e`.
2. Plurality attains the maximum.
   - `labelCount_le_winnerOr`.
   - `jointWeight_le_winnerOr`: `jointWeight π c z d ≤ jointWeight π c z (winnerOr c z)`
     on every word, including the all-abstention word.
3. All-abstention word.
   - `jointWeight_allAbstain`: on that word every label has weight
     `fixCount c * u^n`, i.e. `u^n / M` after normalizing.
   - `card_mul_fixCount`: `M * fixCount c = M!`.
4. Label equivariance, via `plurality_relabel`.
   - `stateAccuracy_eq_voteAccuracy`: in every relabelled state ρ, the
     accuracy equals V_n.
   - `sum_jointWeight_winnerOr`: `∑_z W(z, winnerOr z) = M!·V_n + fixCount c·u^n`.
   - `normalized_J_eq`: `J_n / M! = V_n + u^n / M`. This is Doc B's
     `J_N = V_N + u^N / M`.
5. Product law and max-of-sum.
   - `jointWeight_eq_sum_cons`: `W_N(z,d) = ∑_a W_{N+1}(Fin.cons a z, d)`.
   - `sum_word_succ`: reindexing via `Fin.consEquiv`.
   - `sum_jointWeight_winnerOr_mono`: `J_N ≤ J_{N+1}`.

The headline follows by substituting the identity from step 4 into step 5,
then dividing by `fixCount c > 0` (`fixCount_pos`) and by `M`.

## Axiom check

The check copies the module to `scratch/closeout/modal/AxCheck.lean` with
`#print axioms` appended (exit 0, log `scratch/closeout/modal/axcheck.log`).
Every listed declaration shows `[propext, Classical.choice, Quot.sound]`:
- voteAccuracy_succ_sub_ge, voteAccuracy_le_succ, voteAccuracy_monotone,
  voteAccuracy_succ_sub_eq_of_subsingleton, modalIncrement_nonneg
- jointWeight_le_of_labelCount_le, jointWeight_le_winnerOr,
  jointWeight_eq_sum_cons, jointWeight_allAbstain
- stateAccuracy_eq_voteAccuracy, sum_jointWeight_winnerOr, normalized_J_eq,
  sum_jointWeight_winnerOr_mono, card_mul_fixCount, prod_pow_le_prod_pow_swap

A grep of the final file for sorry, admit, native_decide, decide, axiom,
opaque, implemented_by, extern, unsafe, instance and maxHeartbeats finds nothing.

## Scratch files (all under scratch/closeout/modal/)

Draft.lean, draft.log, final.log, AxCheck.lean, axcheck.log.
