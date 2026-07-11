# RECONCILIATION.md — Phase -1 record

Date: 2026-07-10. Author of record: Kevin Vallier. Formalization thread: Fable
(Claude), per `HANDOFF_STRATEGIC_EVOLUTION_LEAN.md`.

## Search performed (this machine)

- Spotlight (`mdfind`) for `StrategicEvolution`, `SEKernel`, `2512.07901` — no hits
  (note: Spotlight indexing found unreliable on this machine; it missed a file known
  to contain the arXiv id, so direct sweeps were used as the real check).
- Direct `find` over `~/Desktop`, `~/Documents`, `~/Downloads` (depth 3) for
  `*strategic*`, `*SEKernel*` — only the handoff document itself and unrelated files.
- `find ~` (depth 4) for Lean projects (`lakefile.*`, `lean-toolchain`) outside the
  Erdős tree — one hit: `~/mathcode/lean-workspace` (April 2026 MathCode install,
  unrelated problem files; no Strategic Evolution content, checked by grep).
- Content grep over `~/Desktop` and `~/mathcode` for `2512.07901`, `StrategicEvolution`,
  `SEKernel`, `strategic|replicator|lyapunov` in `.lean`/`.md` — no SE-related hits.

**Conclusion: no prior Strategic Evolution Lean artifacts exist on this machine.**

## Prior work referenced by the paper (located on another machine; NOT obtained)

The published paper (arXiv:2512.07901, HTML of 2025-12-15) itself carries
"Formalization:" notes naming these Lean files and their status:

| File | Results covered | Paper-stated status |
|---|---|---|
| `Frontier.lean` | Thm 3.3 (SS-1), 3.5 (SS-2a), 3.6 (SS-2b) | proven **modulo ODE derivative axioms** (Mathlib Analysis.ODE.PicardLindelof) |
| `Sparsity.lean` | Thm 5.2 (ESDI existence), 5.3 (Nash-KKT-LP), 5.4 (sparsity), Cor 5.5 | "fully proven" |
| `SmallGain.lean` | Lem 8.1, Thm 8.2 (G1), 8.6 (G2), 8.9 (G3) | "fully proven" |
| `GInfinityExtension.lean` | Lem 11.3, 11.4, Thm 11.6, 11.7 (G∞) | proven **modulo spectral theory** (Horn–Johnson) |
| `G12ConstitutionalSelection.lean` | Thm 12.1, 12.2 (welfare), 20.3 | proven **modulo ODE well-posedness** |
| `AlignmentImpossibilityProofs.lean` | Lem 14.4, 14.6 | proven **modulo Perron–Frobenius** |
| `PerronFrobenius.lean` | Lem 14.5, Thm 14.7, 14.8 | proven **modulo Perron–Frobenius** |
| `HopfBifurcation.lean` | Prop 16.1, Thm 16.2, 16.3 | proven **modulo center manifold reduction** |

## Author ruling (Phase -1, step 1)

Asked Kevin 2026-07-10 (this session) whether prior artifacts could be produced.
**Ruling: "Reconstruct from scratch"** — prior files not reachable from this machine
now; proceed with Phase 0 and fresh Tier-1 Lean; reconcile later if the files surface.

## REUSE-vs-RECONSTRUCT table

With artifacts unavailable, every target is RECONSTRUCT. The reconstruction is *not*
duplication even if the old files later surface, because the old files (per the
paper's own notes) rest on **custom axioms for the analytic layers** (ODE derivatives,
Perron–Frobenius, center manifolds), while this kernel's contract is **zero custom
axioms on the load-bearing path**. Strategy that makes this possible:

1. **Discrete time / given-trajectory statements** — Lyapunov and elimination claims
   stated either for the discrete-time replicator update (pure Finset algebra) or for
   a trajectory *given as a hypothesis* (no existence/PicardLindelof needed).
2. **Certificate-form small gain** — the paper's own Theorem C.5(3) (M-matrix
   characterization) blesses `∃ v > 0, (I − Γᵀ)v > 0` as equivalent to ρ(Γ) < 1 for
   nonnegative Γ. The kernel takes the certificate as the working hypothesis and
   proves G1/G∞ *unconditionally* from it; row-sum sufficiency (Cor C.3) is proved
   outright; the certificate ⟺ spectral-radius bridge is the one recorded
   spectral-theory interface (Tier 2 / deferred, per handoff fence 2).
3. **Exact quadratic-form statements** for Law 6 local analysis (linearized dynamics)
   instead of `O(‖x−x*‖²)` approximation arguments.

If the prior files are later obtained: inventory (shas, `#print axioms`, sorry scan),
then merge — expected outcome is that this kernel *supersedes* them on axiom hygiene
while they may exceed it in breadth (G2/G3/Hopf statements).

## Source artifact

- `arxiv.org/html/2512.07901` fetched 2026-07-10, sha256
  `c34365bcde1357c84c65ced11c80f31685777c2e90162b1ba11e6d7facdc32dd`
  (kept in session scratchpad as `se_paper.html`; plain-text extraction
  `se_paper.txt` used for statement transcription).
