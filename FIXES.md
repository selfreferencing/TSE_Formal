# FIXES.md — 2026-08-07 fix wave

Response to the independent adversarial audit of 2026-08-07 (`TSE_AUDIT.md`,
kept with the author's working notes).  The audit confirmed the axiom-hygiene
claim (zero custom axioms, zero `sorryAx`, exhaustively over the elaborated
environment) but found two substantive defects and several documentation
failures.  This wave fixes all of them.  Nothing here weakens any previously
proved result; every previously green theorem still compiles unchanged except
where explicitly noted.

Verification state after the wave (all reproducible from a clean checkout):

```
lake build                       →  Build completed successfully
lake env lean AxiomsAudit.lean   →  141 headline theorems, all on
                                    [propext, Classical.choice, Quot.sound]
                                    (admissible_foldr: no axioms at all)
environment sweep                →  240 theorems in SEKernel.*, zero custom
                                    axioms, zero sorryAx, zero nonstandard deps
lake env lean RepairProbe.lean   →  anti-vacuity certificates, clean
grep -rnE "^[[:space:]]*axiom[[:space:]]" --include='*.lean' .
                                 →  no matches (zero axiom declarations)
```

---

## Fix 1 — Law 7: the classical Hopf interface was vacuous (SEVERE)

**Audit finding.**  `ClassicalHopfStatement` was FALSE as stated: `HopfFamily`
carried `α, ω : ℝ → ℝ` as free fields and `ℓ₁` as a bare real, none tied to
the vector field `V`.  The identically-zero field satisfied every hypothesis
(with `α κ = κ`, `ω = 1`, `ℓ₁ = −1`) while having no nonconstant periodic
orbit — machine-checked refutation in the audit's `VacuityProbe.lean`.  Hence
`hopf_transition_conditional` was an implication with a refutable antecedent:
true for every family, carrying no information.

**Repair** (`SEKernel/Law7_Hopf.lean`, rewritten interface section):

* `HopfFamily` now carries the Jacobian `J : ℝ → Matrix (Fin 2) (Fin 2) ℝ`
  together with the proof obligation `hasJac : ∀ κ, HasFDerivAt (V κ)
  (mulVecLin (J κ)).toContinuousLinearMap (equilibrium κ)` — the eigendata is
  a property of `V`, not a free parameter.  Joint smoothness of the family
  (`smooth`) and smoothness of the equilibrium branch (`eqSmooth`) exclude
  the remaining pathological selections.
* The critical linearization is pinned to the rotation frame
  (`J κc = rotation ω₀`, `ω₀ > 0`), which encodes the crossing position AND
  the nonzero frequency, and is exactly the frame in which the
  Guckenheimer–Holmes formula is stated.
* The first Lyapunov number is now a DEFINITION, `ell1At`, computed from the
  second/third-order jet of the shifted field by G–H formula (3.4.11) via
  slice partial derivatives (`p1`, `p2`).  The supercriticality hypothesis
  `ell1At … < 0` therefore constrains `V` itself.
* A new lemma `IsPeriodicOrbit.pushforward` transfers orbits through affine
  coordinate changes, and the repaired `hopf_transition_conditional` packages
  the general-frame case: explicit conjugator `P` with explicit inverse `Q`,
  conjugacy `J κc · P = P · rotation ω₀`, transversal trace crossing, and
  `ell1At` of the conjugated-shifted field negative.

With every datum tied, `ClassicalHopfStatement` IS the planar supercritical
Hopf theorem (G–H Thm 3.4.2 + 3.4.11) — still not in Mathlib, still an
explicit named hypothesis and never an axiom, but now TRUE as stated and
hence meaningful to assume.

**Anti-vacuity certificates** (`RepairProbe.lean`, root):

* `zero_field_fails_rotation` — a family with identically-zero field is
  forced by `hasJac` (uniqueness of the Fréchet derivative) to have zero
  Jacobian, which can never equal `rotation ω₀` with `ω₀ > 0`.
* `linear_field_ell1_zero` / `linear_field_fails_ell1` — every linear planar
  field has `ell1At = 0` exactly, so the supercriticality hypothesis fails;
  the "free ℓ₁" loophole is closed.

Satisfiability of the repaired hypotheses is witnessed constructively by the
instantiation below — the hypothesis set is neither vacuous nor unsatisfiable.

## Fix 2 — Law 7 instantiated: ℓ₁ machine-derived, AQ-20 corrected

**Audit findings.**  (i) `firstLyapunov_neg` was a sign fact about a
*transcribed* formula — nothing tied `firstLyapunovCoeff` to any dynamical
system.  (ii) `rm_true_hopf` (AQ-20's "true Hopf at κ = 0") established
necessary crossing conditions only, at the single parameter point `μ = 0`.

**New module** `SEKernel/Law7_Instantiation.lean`:

* `rmPlanar κ μ` — the planar reduction of the kernel's own replicator–
  mutator field; `rmPlanar_hasJac` proves the kernel's Jacobian entries are
  its true Fréchet derivative at the barycentre (for ALL `κ, μ`);
  `rmPlanar_smooth_rev` gives joint smoothness.
* On the genuine trace-zero locus `κ = −6μ` the Jacobian factors as
  `(1 − 3μ)·J(0,0)`, so ONE conjugator works for every `μ`:
  `Pmat`/`Qmat` with `QP_one`, `PQ_one`, and `rmJ_conj` conjugating to
  `rotation (√3(1 − 3μ)/3)`.
* **`ell1_Wc`** — the first Lyapunov number of the conjugated shifted field
  is the exact identity `μ·(−t⁴ − 2t² − 9)/4` (`t = √3`; the identity holds
  without even using `t² = 3`, and reduces to `−6μ`).  **`ell1_Wc_neg`** —
  strictly negative on all of `μ ∈ (0, 1/3)`.  This is DERIVED from the
  dynamics, replacing the transcription; the quadratic G–H terms cancel
  pairwise, machine-checked.
* **`ell1_pureRPS_zero`** — at `μ = 0` the number is exactly 0: the κ = 0
  crossing of the pure replicator is a DEGENERATE Hopf (the classical RPS
  center with conserved `x₀x₁x₂`), not a generic supercritical one.  This
  **corrects AQ-20**: `rm_true_hopf`'s crossing data stands, but the "true
  supercritical Hopf at κ = 0" reading does not; κ = 0, μ = 0 is the
  degenerate organizing point.
* **`rm_supercritical_hopf`** — the payoff: for every `μ ∈ (0, 1/3)` the
  replicator–mutator undergoes a supercritical Hopf at `κ = −6μ`, with
  nonconstant periodic orbits for every bias just past threshold,
  **conditional only on `ClassicalHopfStatement`** — every other hypothesis
  is machine-discharged.  As `μ → 0⁺` the locus converges to κ = 0, the
  γ = 1 boundary, recovering the AQ-20 picture as a degenerate limit.

**Recommendation to the author (supersedes the AQ-20 paper fix).**  State
Law 7's transition for the canonical model at the locus `κ = −6μ`
(equivalently: trace zero at mutation-selection balance), supercritical with
machine-derived `ℓ₁ = −6μ` (G–H normalization), frequency
`ω₀ = √3(1 − 3μ)/3`; describe γ = 1 (κ = 0, μ = 0) as the degenerate
center limit of the locus.  The printed κ_c(μ) formula remains refuted
(`rm_no_hopf`, unchanged).

## Fix 3 — Law 3: the spectral interface (AQ-9) is CLOSED, both directions

**Audit finding.**  The paper states Law 3 spectrally ("stable iff spectral
radius of the normalized gain matrix < 1") but the kernel proved only
certificate-form results; the certificate ⟺ ρ(Γ) < 1 bridge was deferred, so
the law as titled was proven in neither direction.

**New module** `SEKernel/Law3_SpectralClosure.lean` — zero custom axioms,
no Perron–Frobenius input:

* `spectral_bound_of_cert` — certificate with margin `m > 0` ⟹ every complex
  eigenvalue of Γ has modulus ≤ 1 − m/vmax < 1.  (Diagonal similarity turns
  the certificate's column margins into row-sum slack; the Gershgorin-type
  bound of `SpectralBridge` finishes.)
* `cert_of_spectral` — all eigenvalues strictly inside the unit disc ⟹ a
  positive-margin certificate exists.  Proof: Gelfand's formula yields `N`
  with `‖(Γᵀ)^N‖ < 1`; the finite Neumann sum `v = Σ_{k<N} (Γᵀ)^k 𝟙` is a
  positive weight vector with margin `1 − ‖(Γᵀ)^N‖`.
* `cert_iff_spectral` — the equivalence: paper Thm C.5 (2) ⟺ (3) for
  nonnegative gain matrices.  AQ-9 is no longer an interface; it is a
  theorem.
* `G1_weighted_lyapunov_of_spectral` — **Law 3 in its own spectral
  phrasing**: eigenvalues of the normalised gain matrix inside the unit disc
  imply the G1 weighted Lyapunov inequality.
* Supporting: `spectrum_transpose` (spectrum invariant under transposition,
  determinant argument).

The stability direction of the "iff" is now: ρ(Γ) < 1 (eigenvalue form) ⟹
certificate ⟹ G1 Lyapunov.  The instability side remains covered by Law 6's
eigen-witness `lyapunov_destruction` (unchanged).

## Fix 4 — legacy/: DELETED

**Audit findings.**  The directory held the only two `axiom` declarations in
the checkout.  One of them, `eventually_not_hurwitz`, omitted the
`α(J₁) > 0` hypothesis its own docstring named, which made it
**inconsistent** — `False` was machine-derivable from it (audit
`LegacyProbe.lean`).  `legacy/CertificateFrontier.lean` additionally failed
to compile at the pinned Mathlib (dead
`Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup` import, nonexistent
`Matrix.spectrum`, renamed `Set.eq_empty_iff_forall_not_mem`, missing
`Matrix` scope for `ᵀ`).

**Resolution — the directory is removed.**  The files were imported by
nothing, were roots of no `lean_lib`, and were never elaborated by
`lake build`; they could not affect any result, and the exhaustive
environment sweep confirms nothing ever depended on them.  But their mere
presence contradicted the headline claim at a glance: a reader grepping this
repository for `axiom` got two hits and a paragraph of explanation instead
of zero hits.  Since they carried no verification weight, deletion strictly
dominates repair.

A reader can now confirm the claim directly:

```bash
grep -rnE "^[[:space:]]*axiom[[:space:]]" --include='*.lean' .   # no matches
```

(An unanchored `grep -rn axiom` still matches the *word* in prose and in the
`#print axioms` audit directives — those are documentation and audit
commands, not declarations.)

## Fix 5 — documentation: the number "73" and stale protocol text

**Audit finding.**  "73" was the length of the `AxiomsAudit.lean` list at the
2026-07-10 commit — never a theorem count (that commit already had 95
source theorems) — and the current library had 143+8 source declarations,
123 audit entries, 210 environment theorems.  README repeated the stale
number twice.

**Repair.**  README now states the counts as of this wave (203 source
theorem/lemma declarations, 240 environment theorems, 141 audit entries),
labels them with their date, and directs readers to regenerate rather than
trust frozen numbers.  `AxiomsAudit.lean` gained the 19 new headline
entries.  `RETURN.md` is a dated return document and is left as the
historical record of the 2026-07-10 state; this file is the delta.

## Not changed

* All previously verified theorems in Laws 1–6, PriceMarket(Master),
  WaterLine, SpawnConflict, SpectralBridge — untouched.
* `hopfCurve`, `hopfCurve_pos`, `hopfCurve_root`, `firstLyapunov_neg` —
  retained as facts about the paper's printed formulas (their role is
  documentary; the derived `ell1_Wc` now carries the dynamical content).
* `rm_no_hopf` — the refutation of the printed κ_c(μ) locus stands.
* `rm_true_hopf` — the crossing data at κ = 0, μ = 0 stands; its
  interpretation is corrected by `ell1_pureRPS_zero` (degenerate, not
  generic).
* The four named classical inputs (LP strong duality, Brouwer, the Lemma
  15.3 interface, classical planar Hopf) remain hypotheses, never axioms;
  the spectral-radius interface is no longer among them.

## Known remaining gaps (honest ledger)

* `ClassicalHopfStatement` itself — the one remaining classical input for
  Law 7; formalizing it is the well-defined future target.
* Second Welfare converse (separating hyperplane), LaSalle (Cor 3.4), G2/G3,
  Thm 16.3 amplitude scaling — deferred as before.
* `PriceMarketMaster.l1Symmetric` is still a definition whose derivation
  lives outside the repo; the `ell1At` machinery introduced here is the tool
  to derive it once the concrete coupled field is pinned down (the module
  defines only the Jacobian, not the nonlinear field).
* Orbital stability of the bifurcating cycle is part of the classical
  conclusion and is not re-stated in the kernel's `IsPeriodicOrbit`.
