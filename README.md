# TSE Formal — Lean 4 / Mathlib verification of the Seven Laws of Strategic Evolution

Machine-verified kernel of the formal backbone of Kevin Vallier, *The Theory of
Strategic Evolution: Games with Endogenous Players and Strategic Replicators*
(arXiv:2512.07901).

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0--rc1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-green.svg)](https://github.com/leanprover-community/mathlib4)

---

## What this is

**All seven laws carry machine-verified content, cold-compiling with zero
custom axioms** — 203 theorem/lemma declarations in source, 240 theorems in
the elaborated environment, every one depending only on Lean/Mathlib's
standard base (`propext`, `Classical.choice`, `Quot.sound`); a handful need
no axioms at all. No `sorry`, no `admit`, no `native_decide`, no custom
`axiom` anywhere on the load-bearing path — verified exhaustively over the
environment, not just over a name list. This is a from-scratch
reconstruction that deliberately avoids the "modulo ODE / Perron–Frobenius /
spectral-theory axioms" caveats of earlier drafts — the analytic content is
replaced by exact, discrete, or certificate-form statements that are
provable outright, with the small number of genuinely classical inputs
(LP strong duality, Brouwer, the classical planar Hopf theorem) carried as
explicit *hypotheses* rather than axioms.  (Counts as of the 2026-08-07 fix
wave; regenerate with the audit commands below rather than trusting any
frozen number.)

**2026-08-07 fix wave** (see [`FIXES.md`](FIXES.md)): the certificate ⟺
spectral-radius interface of Law 3 (AQ-9) is now **proved in both
directions** with zero custom axioms (`Law3_SpectralClosure.lean`); Law 7's
classical-Hopf interface was **re-architected to be non-vacuous** — every
piece of eigendata is now tied to the vector field, the first Lyapunov
number is machine-DERIVED from the replicator–mutator dynamics
(`ell1At = −6μ` on the genuine locus `κ = −6μ`), and the degenerate center
at `κ = μ = 0` is identified (`Law7_Hopf.lean`, `Law7_Instantiation.lean`,
`RepairProbe.lean`).

The design contract, deviations, and per-law status live in three documents:

- [`STATEMENTS.md`](STATEMENTS.md) — theorem-by-theorem transcription of the
  paper's claims into the exact statements the Lean proves, with the ambiguity
  ledger (AQ-1 … AQ-20) and every recorded deviation.
- [`RETURN.md`](RETURN.md) — per-law verification status, the axiom audit
  protocol, artifact hashes, the repairs, and plain-language summaries.
- [`RECONCILIATION.md`](RECONCILIATION.md) — provenance and the relationship to
  the earlier partial formalization described in the paper's own notes.

## The Seven Laws

| Law | Module | Status |
|-----|--------|--------|
| 1 — Strategic Selection (SS-1 Lyapunov, SS-2 elimination, Basin Limitation) | [`Law1_Selection.lean`](SEKernel/Law1_Selection.lean) | **Cold-verified** (discrete-time form) |
| 2 — ESDI Characterization (Nash / KKT / LP, sparsity, existence) | [`Law2_ESDI.lean`](SEKernel/Law2_ESDI.lean) | **Cold-verified**; LP strong duality carried as a hypothesis |
| 3 — H-γ Stability (small-gain / G1 Lyapunov) | [`Law3_Stability.lean`](SEKernel/Law3_Stability.lean), [`Law3_SpectralClosure.lean`](SEKernel/Law3_SpectralClosure.lean) | **Cold-verified**, now in BOTH forms: certificate ⟺ ρ(Γ) < 1 proved outright (AQ-9 closed, 2026-08-07), so the law's own spectral phrasing is a theorem |
| 4 — G∞ Closure (block extension, slack budget, no infinite regress) | [`Law4_ClosureG.lean`](SEKernel/Law4_ClosureG.lean) | **Cold-verified** |
| 5 — Constitutional Duality (welfare theorems, price of anarchy) | [`Law5_Duality.lean`](SEKernel/Law5_Duality.lean) | **Cold-verified** |
| 6 — Alignment Impossibility (+ Endogenous-Electorate) | [`Law6_Alignment.lean`](SEKernel/Law6_Alignment.lean) | **Cold-verified** |
| 7 — Hopf Transition | [`Law7_Hopf.lean`](SEKernel/Law7_Hopf.lean), [`Law7_Instantiation.lean`](SEKernel/Law7_Instantiation.lean) | **Cold-verified** to Mathlib's edge; classical planar Hopf theorem carried as the ONE hypothesis, now stated non-vacuously with all eigendata tied to the field (2026-08-07); every side condition machine-discharged for the replicator–mutator, ℓ₁ machine-derived |
| — | [`SpectralBridge.lean`](SEKernel/SpectralBridge.lean) | Corrected spectral bounds for Laws 3/4 |
| — | [`RepairProbe.lean`](RepairProbe.lean) | Anti-vacuity certificates: the audit's zero-field / linear-field attacks provably fail the repaired Law 7 hypotheses |

## Findings surfaced by the verification

Formalizing the paper turned up three fixable issues in the preprint and
resolved two model questions — each machine-checked, each with a recommended
correction (details in `RETURN.md` and `STATEMENTS.md`):

- **Law 2 (ESDI existence).** The published extreme-value-theorem proof does
  not yield the equilibrium conditions for state-dependent fitness; a
  counterexample to the proof *method* is machine-checked, and the fix (Nash's
  improvement map, reducing existence to Brouwer's fixed-point theorem) is
  proved by pure algebra.
- **Law 4 (G∞).** Two spectral displays in the published proof are incorrect
  as printed; `SpectralBridge.lean` supplies corrected, verified bounds, and an
  exact certificate-form extension lemma delivers the intended conclusions.
- **Law 6 (Endogenous Electorate).** Anonymity + neutrality are formally
  contradictory for a resolute rule at every number of alternatives ≥ 2; the
  impossibility is rebuilt on an *Overwhelming-Bloc* axiom ("a large enough
  spawned bloc wins its top choice") — the strategic-replicator thesis itself
  — and reproved with no classical inputs, with majority rule witnessing
  consistency.
- **Law 7 (Hopf).** Under the canonical replicator–mutator dynamics the printed
  bifurcation curve κ_c(μ) is *not* a Hopf locus (verified), but a genuine
  supercritical Hopf *does* occur at κ = 0 — exactly the γ = 1 stability
  boundary that Law 7's title names. Center eigenvalues, frequency, and
  transversality are all machine-checked. Recommendation: state the transition
  at γ = 1.

## Building and checking

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager). The toolchain and Mathlib revision are pinned in `lean-toolchain` and
`lakefile.toml`.

```bash
lake exe cache get      # fetch prebuilt Mathlib oleans
lake build              # compile all seven laws (≈ full Mathlib build the first time)
lake env lean AxiomsAudit.lean   # print the axiom dependencies of every headline
lake env lean RepairProbe.lean   # anti-vacuity certificates for the Law 7 interface

# zero custom axioms, checkable directly — this must print nothing:
grep -rnE "^[[:space:]]*axiom[[:space:]]" --include='*.lean' .
```

(An unanchored `grep -rn axiom` will still match the *word* in prose and the
`#print axioms` directives. Those are documentation and audit commands, not
declarations. The anchored pattern above is the claim.)

`AxiomsAudit.lean` runs `#print axioms` on the 141 headline theorems; a
clean run reports `[propext, Classical.choice, Quot.sound]` for each (and
"does not depend on any axioms" for `admissible_foldr`). That printout *is*
the verification claim — it is reproducible from a clean checkout, and an
exhaustive environment-level sweep (every `SEKernel.*` theorem, not just the
audit list) reports zero custom axioms and zero `sorryAx` dependencies.

## Relationship to the paper

The Lean statements are the contract in `STATEMENTS.md`, not a paraphrase.
Where the discrete-time or certificate form deviates from the paper's
continuous-time or spectral phrasing, the deviation is recorded there with its
rationale. The paper is arXiv:2512.07901; its LaTeX source and the
author-facing writeup live in the companion
[`TSE_Paper`](https://github.com/selfreferencing/TSE_Paper) repository.

## License

Following the paper. See the author, Kevin Vallier.
