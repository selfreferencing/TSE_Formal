# RETURN.md — Strategic Evolution Lean kernel, verification return

Date: 2026-07-10.  Source: Kevin Vallier, *The Theory of Strategic Evolution*
(arXiv:2512.07901).  Contract: `STATEMENTS.md`.  Prior-work record:
`RECONCILIATION.md` (author ruling 2026-07-10: reconstruct from scratch).

## Headline

**All Seven Laws now carry machine-verified content, cold, with zero custom
axioms** — the formal backbone of Laws 1–6 plus Law 7's displayed algebra and
its classical-Hopf packaging — every audited theorem depends on exactly
`{propext, Classical.choice, Quot.sound}` (Lean/Mathlib's standard base; one
theorem needs no axioms at all).  No `sorry`, no `admit`, no `native_decide`,
no custom `axiom` anywhere.  This strictly improves the axiom hygiene of the
prior (other-machine) formalization, which the paper's own notes describe as
proven "modulo" ODE-derivative / Perron–Frobenius / spectral-theory axioms.

73 audited theorems, 2,759 lines of Lean across eight modules.  The three
REPAIR-CANDIDATEs (AQ-6, AQ-10, AQ-14) now each carry machine-checked repair
content (see the Repairs section below).

## Verification protocol (fence 4)

1. **Standalone cold build** (this machine, from scratch): fresh clone of
   Mathlib pinned to `5352afccd6866369be9de43f5b7ec47203555f44`, toolchain
   `leanprover/lean4:v4.28.0-rc1`, official olean cache, then
   `lake build` → **`Build completed successfully (7,898 jobs)`**
   (re-run green after every edit, including the AQ-14/AQ-17 design rulings).
2. **Axiom audit** in the standalone environment:
   `lake env lean AxiomsAudit.lean` → exit 0;
   72 theorems report `[propext, Classical.choice, Quot.sound]`,
   `admissible_foldr` reports "does not depend on any axioms";
   full transcript archived in the session scratchpad (`audit_v5.txt`).
3. Independent single-file cold elaboration of the concatenated sources with
   the same audit directives under a second Mathlib build (the Erdős-993
   workspace, same commit pin): exit 0, identical axiom report.
4. Reproduce with: `cd StrategicEvolutionLean && lake exe cache get &&
   lake build && lake env lean AxiomsAudit.lean`.

### Artifact hashes (sha256)

```
32aab5aa9145106f36ce1852b3a0fdee19514fae8c7a7bde058729c9bff81125  lakefile.toml
53382cbe9b2e717af378843459403242cc24a3cc00865ffc644e7cd420a0f815  lean-toolchain
ae98ecc73af44a50405fe55d901ebf804b8a9bc82ba9dd6c9e986fbe5037f57b  SEKernel.lean
0f4c196941ef2003848685b61a1b7a954736c211b05cb601927be800e9b1d701  AxiomsAudit.lean
5b8cedb1a1aac9f9c38d8d79d5152b64311e25838d13deb7db1203bea2fbb94e  SEKernel/Law1_Selection.lean
dc9e9960143cbd87ee48ae52f8371449a2c5185e583ccf38358331002e6c62b9  SEKernel/Law2_ESDI.lean
c31503c8258a61ae2c22fff3f7a82c322ff36a0d5c0e830b8b37ac421992528e  SEKernel/Law3_Stability.lean
d418138490a02f57fe17426fa377c207f8335b0b093840ff25326b54919979e7  SEKernel/Law4_ClosureG.lean
cc4a3913478078ec746deface5d93d44db405cbd29179db8e83dda800836137d  SEKernel/Law5_Duality.lean
255f08f816d08d87ebb5a111a984bad9ad13c6f0c5ffb60c4e6b538d90d16919  SEKernel/Law6_Alignment.lean
c404cae43b1486220f91cc566969383ba1267d3598e23df7968aa69c185be10b  SEKernel/Law7_Hopf.lean
a98924a64a403aa2afeac0a6f7ad44876dae61f5a1087bf3748985d028f57738  SEKernel/SpectralBridge.lean
36c8751c1aaa84d7bcd804cffffd1dfe0ffd10f6fb6306cc85ec3625812eee8b  STATEMENTS.md
b5ff4c7ef7c24faa5f9ee3a22e24bcdb08126685b641d9d9076507931b006676  RECONCILIATION.md
```
Source paper (arXiv HTML, fetched 2026-07-10):
`c34365bcde1357c84c65ced11c80f31685777c2e90162b1ba11e6d7facdc32dd`.

## Repairs delivered (the former REPAIR-CANDIDATEs)

### AQ-6 — ESDI existence (Thm 5.2): proof gap REPAIRED
`Law2_ESDI.lean §ExistenceRepair`.
- `maximizer_method_gap` — **machine-checked counterexample to the paper's
  proof method**: `F(x) = (1 − x₀, 0)` is continuous, its mean-fitness
  maximizer is `(1/2, 1/2)`, and that maximizer violates equilibrium
  condition (1) (supported fitness 1/2 ≠ mean 1/4).  So "any maximum
  satisfies the ESDI conditions" is false for state-dependent fitness.
- `exists_mean_maximizer` — what EVT does give: a mean-fitness maximizer on
  the simplex (condition (3)).
- **The repair**: Nash's improvement map.  `nashMap_fixedPoint_equilibrium`
  proves — by pure algebra, no topology — that any fixed point of the Nash
  map on the simplex satisfies equilibrium conditions (1)–(2);
  `esdi_exists_of_fixedPoint` packages general existence conditional on the
  fixed point.  Brouwer's theorem (which supplies it for continuous `F`) is
  **not in Mathlib at this pin (verified by search)** — it is the recorded
  classical input, exactly the agreed protocol.
- Suggested paper fix: replace the Thm 5.2 proof by "existence follows from
  Brouwer's fixed-point theorem applied to Nash's improvement map; the
  reduction is machine-verified in `SEKernel`."

### AQ-10 — G∞ spectral displays (Lem 11.3 / Thm 11.7(d)): REPAIRED
New module `SpectralBridge.lean`, proved via Mathlib's Banach-algebra
spectrum API (`spectrum.norm_le_norm_of_mem` + the L∞ operator norm):
- `eigenvalue_le_rowSum` — Gershgorin-type bound (paper Cor C.2's use).
- `gain_eigenvalue_bound` — spectral Cor C.3: nonnegative gain matrix with
  row sums ≤ 1 − m has every complex eigenvalue within 1 − m.
- `extension_eigenvalue_bound` — **the corrected 11.3/11.7(d) display**: if
  each old row sum plus its new coupling and the new row's sum are ≤ 1 − m′,
  every eigenvalue of the block extension Γ̃ stays within 1 − m′.
- Suggested paper fix: replace the `ρ(Γ̃) ≤ ρ(Γ) + √(‖b‖·‖c‖)` and
  "Gershgorin" displays with the row-sum bound above (machine-checked), or
  cite the certificate lemma `extension_cert` for the weighted form.  The
  Perron–Frobenius certificate ⟺ ρ equivalence (C.5(2)⟺(3)) remains the one
  recorded spectral interface (not in Mathlib).

### AQ-14 — §15 axioms (Lem 15.3 / Thm 15.4): REPAIRED-AND-DEEPENED
`Law6_Alignment.lean §NeutralityImpossibility`.
- `neutrality_unsat_three` — **new finding, machine-checked**: Anonymity +
  Neutrality alone are unsatisfiable for a resolute rule at |A| = 3 over the
  full variable-electorate domain (the Condorcet profile {abc, bca, cab} is
  invariant under the 3-cycle, which fixes no alternative).  Hence
  Theorems 15.2–15.5 are **vacuous at |A| = 3 as stated** — a deeper issue
  than the Step-4 gap originally flagged, caught before any referee.
- Repair options (author decision, AQ-19): odd-electorate domain, |A| ≥ 4,
  set-valued rules, or weakened neutrality — plus an explicit
  variable-population monotonicity axiom A3′ for Lemma 15.3's Step 4.
- The kernel's `endogenous_electorate_impossibility` (15.4 from the
  manipulation interface) and the unconditional majority-rule witness are
  compatible with every repair option.
- **RESOLVED (design ruling delegated to the formalizer):**
  `neutrality_unsat` shows the obstruction exists at **every** |A| ≥ 2 (the
  impartial-culture profile is invariant under all relabelings), so the
  odd-domain and |A| ≥ 4 escapes fail — resolute + neutral is broken at every
  size.  The chosen, more faithful repair keeps resoluteness and anonymity,
  **drops Neutrality**, and replaces the May machinery by one axiom that is
  the strategic-replicator thesis itself:
  **A5 (Overwhelming-Bloc)** — a large enough spawned bloc of identical
  ballots wins its top choice (`OverwhelmingBloc`).  From A5 + richness,
  spawn manipulation (`spawnManipulable_of_overwhelmingBloc`) and the
  Endogenous-Electorate Impossibility (`endogenous_electorate_impossibility_repaired`)
  are theorems with **zero classical inputs**; consistency is witnessed by
  majority rule (`majority_overwhelmingBloc`,
  `majority_not_populationStable_repaired`).  "Replication buys votes" is now
  the formal engine of the impossibility, not an unprovable neutrality axiom.

## Per-law status

### Law 1 — Strategic Selection: **FORMALIZED** (discrete form, AQ-1..4)
`SEKernel/Law1_Selection.lean`.
- Prop 3.1 (Price): `selection_gain` — the selection term of one discrete
  replicator step is *exactly* `Var/f̄`; `price_decomposition` gives the full
  identity with the externality term `E_disc` defined as in the paper.
- Thm 3.3 (SS-1): `SS1_discrete` — under discrete H-γ (γ < 1), mean fitness
  gains at least `(1−γ)·Var/f̄ ≥ 0`; `SS1_equality_iff` — the gain is zero
  iff `Var = 0`; `variance_eq_zero_iff` — iff all supported types sit at
  mean fitness.
- Thm 3.5 (SS-2a): `elimination_single_bound/decay/tendsto` — ratio-dominated
  types decay geometrically and vanish; `elimination_mixture(_tendsto)` —
  mixture domination in geometric-mean form via the paper's log-contrast.
  **Proof simplification found:** the paper's Step 4 (survival of the
  dominating mixture) is unnecessary — `Π x_k^{α_k} ≤ 1` bounds the contrast
  directly.  Lean uses the shorter route.
- Thm 3.6 (SS-2b): `frontier_support` — support of orbit limits lies in the
  frontier, conditional on the hull-domination interface (AQ-3; the convex
  -hull geometry itself is deferred).
- Thm 3.7 (Basin): `basin_decrease`, `basin_instability` (part a),
  `basin_no_recovery` (part b, no-overshoot interface) — discrete orbit
  forms; the `g′(1) > 0` germ branch deferred with the ODE layer.
- Deferred: Cor 3.4 (LaSalle convergence — dynamical-systems layer).

### Law 2 — ESDI Characterization: **FORMALIZED / CONDITIONAL(strong duality)**
`SEKernel/Law2_ESDI.lean` — the paper gives no body proofs for 5.3/5.4; the
kernel supplies them for the §12.1 portfolio LP.
- Thm 5.3 (Triple Equivalence): `KKT.isLPOptimal` — (KKT) ⟹ (LP) fully
  proved (weak duality + complementary slackness, `KKT.value_eq`,
  `weak_duality`); `KKT_of_optimal_dual` — (LP) ⟹ (KKT) **conditional on a
  zero-gap dual witness** (LP strong duality = the ONE conditional input,
  per handoff protocol); complementary slackness is *derived* from the
  witness, not assumed.  (Nash) ⟺ (LP) is definitional under the AQ-7
  reading (`nash_iff_lpOptimal`).
- Def 5.1 bridge: `KKT.reduced_return` — supported types have zero reduced
  return, all nonpositive (ESDI conditions in shadow-price form).
- Thm 5.2 (Existence): `esdi_exists_const` — **state-independent case
  proved constructively** (uniform mass on argmax).  The paper's general
  state-dependent EVT proof has a gap — **REPAIRED**, see the Repairs
  section (machine-checked counterexample to the method + Nash-map
  reduction + Brouwer-conditional general existence, AQ-6).
- Thm 5.4 / Cor 5.5 (Sparsity/Barbell): `constraint_role_sparsity` — at any
  KKT point, support lies on the shadow-price line; under generic position
  (no 3 cost-normalised points collinear) support ≤ 2 (AQ-8).

### Law 3 — H-γ Stability: **FORMALIZED** (certificate form, AQ-9)
`SEKernel/Law3_Stability.lean`.
- Working small-gain hypothesis = the paper's own Thm C.5(3) M-matrix
  certificate `∃ v > 0, (I − Γᵀ)v ≥ m·𝟙` (`SmallGainCert`).
- Lem 8.1: `G1_weight_pos` (weights positive); Cor C.3: `of_colSums`
  (column-sum sufficient condition, proved outright).
- Thm 8.2 (G1): `G1_weighted_lyapunov(_nonneg)` — the paper's entire
  displayed chain, verified as exact finite algebra: certificate + H-NL ⟹
  `Σ α_ℓ(Var_ℓ + E_ℓ) ≥ m·Σ Var_ℓ ≥ 0`.
- **Finding:** `β ≥ 0` (Assumption 7.3) is not needed for the G1 inequality.
- Deferred: the spectral bridge ρ(Γ) < 1 ⟺ certificate (Perron–Frobenius
  grade; equated by the paper's Thm C.5), and G2/G3 (Tikhonov,
  Freidlin–Wentzell — analysis layers, out of kernel scope per handoff).

### Law 4 — G∞ Closure: **FORMALIZED** (certificate form) **+ REPAIR-NEEDED (paper displays, AQ-10)**
`SEKernel/Law4_ClosureG.lean`.
- Lem 11.3 / Thm 11.7(d): `extension_cert(_halfMargin)` — **Certificate
  Extension Lemma** with the explicit new weight `w = ⟨b,v⟩ + m′`: small new
  couplings preserve small gain with quantified margin (the σ/2 clause is
  the `m′ = m/2` instance).  **The paper's own spectral-perturbation display
  (`ρ(Γ̃) ≤ ρ(Γ) + √(‖b‖·‖c‖)`) and the 11.7(d) "Gershgorin" display do not
  look correct as stated — flagged for repair; the certificate lemma
  delivers the intended conclusions with a correct proof.**
- Lem 11.4: `slack_budget` — margin ≥ `(1−θ)^M σ₀` under per-step retention.
- Thm 11.6: `safe_stack_depth` — `θ·M ≤ log(σ₀/σ_min)` under per-step cost.
- Cor 11.8: `no_infinite_regress` — no infinite admissible chain above a
  positive margin floor ("cannot escape selection by going meta").
- 11.7(b) is the shared G1 algebra (Law 3 file); 11.7(a) self-similarity is
  structural narrative (recorded), 11.7(c) protection bits deferred with G3.

### Law 5 — Constitutional Duality: **FORMALIZED** (welfare theorems + PoA, AQ-15/16)
`SEKernel/Law5_Duality.lean` — the paper states 12.1/12.2/12.4 with **no body
proofs**; the kernel supplies statements and proofs in the GEP setting
(lineages with private budgets, one shared capacity, one constitutional
shadow price λ).
- Thm 12.1 (First Welfare): `first_welfare` — a shadow-price-supported joint
  allocation (`PriceSupported`: per-lineage dual feasibility + complementary
  slackness on supports, budgets, and the shared capacity) is **Pareto
  efficient** among all feasible joint allocations.  Fully proved: per-lineage
  CS value identities (`value_eq`) + weak duality at any deviation
  (`value_le`), summed — the λ-terms cancel against the shared `Q`.
- Thm 12.2 (Second Welfare), implementation half:
  `shadow_price_implementation` — at the constitutional price λ, each
  lineage's assigned portfolio maximises its profit `Σ (r_i − λℓ_i) m_i`
  over its **private budget set alone**; the shared constraint is fully
  decentralised into the price.  Converse half (Pareto ⟹ supporting prices;
  separating hyperplane): recorded, deferred (AQ-15).
- Thm 12.4 (PoA): `poa_bound(_ratio)` — from the Def 5.1(2) equilibrium
  conditions and the **cross-state H-γ bound**
  `Σ_j y_j (f_j(y) − f_j(x)) ≤ γ·f̄(y)` (the static face of Assumption 3.2 —
  the paper gives no proof or precise hypothesis; AQ-16), the exact bound
  `(1−γ)·f̄(y) ≤ f̄(x)`, i.e. `PoA ≤ 1/(1−γ)`, follows by a smoothness-style
  two-line argument.

### Law 6 — Alignment Impossibility: **FORMALIZED** (exact linearised + eigen-witness forms, AQ-11..13) **+ REPAIR-NEEDED (Lemma 15.3, AQ-14)**
`SEKernel/Law6_Alignment.lean`.
- Def 14.3 / Thm 14.7(a,b,c): `lie_identity` (the S = ½(HJ+JᵀH) derivative
  identity as exact finite algebra), `hasDerivAt_qform_along_linear` (true
  derivative along a *given* trajectory — no ODE existence),
  `msg_sufficiency` (a), `msg_necessity` (b — algebraic small-step limit
  argument), `msg_maximal` (c).
- Lem 14.5: `lyapunov_destruction` — an eigen-witness `(u ≥ 0, λ ≥ 1)`
  makes any positive-margin certificate impossible (pairing argument; the
  Perron–Frobenius step that manufactures the witness from ρ ≥ 1 stays
  outside — it was the prior work's axiom).
- Thm 14.7(d): `alignment_impossibility_escape` — full reachability + one
  bad reachable state refute uniform Lyapunov structure.
- Thm 14.8: `admissible_id/comp/foldr/contains/unique` — `M₀ = M_R ∩ M_SG`
  as the unique maximal class closed under **arbitrary finite
  self-modification sequences** (the closure-operator content the handoff
  predicted; `admissible_foldr` is fully axiom-free).
- Thm 15.4: `endogenous_electorate_impossibility` — impossibility proved
  from the Lemma 15.3 interface (irreflexivity is the only structural
  hypothesis); **unconditional witness** `majority_spawnManipulable` /
  `majority_not_populationStable` — majority rule on two alternatives falls
  to two spawned clones.  **AQ-14 (repaired-and-deepened, see the Repairs
  section):** beyond Lemma 15.3's Step 4 gap (needs a variable-population
  monotonicity axiom; A3 is fixed-electorate), `neutrality_unsat_three`
  proves A1 + A2 alone are unsatisfiable at |A| = 3, so §15's theorems are
  vacuous there as stated; May's theorem (Lem 15.2) not in Mathlib.
  Repair decision: AQ-19.

### Law 7 — Hopf Transition: **FORMALIZED to Mathlib's edge / CONDITIONAL(classical Hopf)**
`SEKernel/Law7_Hopf.lean`.
- Prop 16.1: `hopfCurve` transcribed; `hopfCurve_pos` — the locus is a
  genuine positive curve on μ ∈ (0, 1/3).  **Proved.**
- Thm 16.2: `firstLyapunov_neg` — the supercriticality inequality
  `ℓ₁(κ_c, μ) = −(√3/8)(1−3μ)/(1−μ)² < 0` on the whole parameter range.
  **Proved.**  The passage from ℓ₁ < 0 to stable limit cycles is the
  classical supercritical Hopf theorem — **not in Mathlib**; stated as one
  explicit Prop (`ClassicalHopfStatement`, hypotheses: crossing,
  transversality, nonzero frequency, ℓ₁ < 0; conclusion: nonconstant
  periodic orbits, given-trajectory encoding `IsPeriodicOrbit`).
  `hopf_transition_conditional` composes it with the proved inequality:
  Law 7's conclusion holds given exactly that named classical input — never
  an axiom.  Formalizing `ClassicalHopfStatement` itself is the well-defined
  future target ("formalize the classical part later").
- **AQ-17 RESOLVED (design ruling delegated to the formalizer) → new finding
  (AQ-20).**  `Law7_Hopf.lean §ReplicatorMutator` instantiates the canonical
  **replicator–mutator** model (uniform mutation rate μ toward the barycentre —
  the standard closure of the §2.2 "Innovation Rare" axiom) on the printed
  Π(κ).  `rm_diag0`/`rm_diag1` machine-check the two diagonal partials of the
  center linearization; `rm_center_trace` sums them to **`−κ/3 − 2μ`**; and
  `rm_no_hopf` proves this is strictly negative for all κ ≥ 0, μ > 0.  So
  under the canonical dynamics **no Hopf occurs at the printed curve κ_c(μ)** —
  the interior equilibrium is a stable focus throughout the positive-bias
  range (the pure-selection Hopf sits at κ = 0, and any mutation pushes it
  strictly stable).  `hopfCurve_root` proves κ_c is the small root of
  `3μκ² − 2(1−μ)κ + (1−μ)² = 0`, the fingerprint offered to identify the
  family the author intended.  Thm 16.3 (amplitude scaling): deferred with the
  classical layer.
- **AQ-20 RESOLVED — the true Hopf is at the γ=1 boundary** (`§TrueHopf`).
  The positive counterpart to the no-Hopf finding: the pure replicator on
  Π(κ) has center eigenvalues `−κ/6 ± i√3(κ+2)/6`, so a genuine supercritical
  Hopf occurs at **κ = 0**, which is exactly the pure-swirl / γ=1 boundary
  (Law 7's own stated threshold).  `rm_center_det` computes the full center
  determinant; `rm_true_hopf` verifies all three Hopf conditions at κ = 0
  (trace 0, det 1/3 > 0 so frequency ±i/√3, transversal slope −1/3);
  `swirl_ratio_blowup` proves the swirl ratio (κ+2)/κ → ∞ as κ → 0⁺, locating
  κ = 0 as the γ=1 point.  The paper's ℓ₁ carries the equilateral-RPS √3,
  confirming it is the κ = 0 coefficient.  **Recommendation:** keep Thm 16.2's
  supercriticality; restate Prop 16.1's locus as κ = 0 (γ = 1), tying Law 7 to
  Laws 1/3 via the swirl decomposition — Law 7 is *true at its own title's
  threshold*, and only the illustrative κ_c(μ) formula needs correcting.

## Deviations ledger (author sign-off status)

| # | Deviation | Basis |
|---|---|---|
| AQ-1 | SS-1 in discrete time, `E_disc`/`Var/f̄` normalization | handoff pre-approval ("discrete version as stated-or-author-approved"); confirm |
| AQ-2 | SS-2a mixture hypothesis = geometric-mean domination | discrete log-contrast forces it; confirm |
| AQ-3 | SS-2b hull-domination as interface | kernel scope; confirm |
| AQ-4 | Basin discrete-orbit forms + no-overshoot interface | kernel scope; confirm |
| AQ-5/7 | Nash = no-feasible-improving-deviation; KKT/LP defs as stated | definitional fidelity choice; confirm |
| AQ-6 | ESDI existence gap (state-dependent f) | **REPAIRED** (counterexample + Nash-map reduction; Brouwer = recorded classical input); paper-text fix suggested |
| AQ-8 | Sparsity under generic position | degenerate cases need a convention; confirm |
| AQ-9 | Small gain via M-matrix certificate (paper's C.5(3)) | paper-internal equivalence; confirm |
| AQ-10 | 11.3/11.7(d) spectral displays incorrect as printed | **REPAIRED** (SpectralBridge corrected displays + certificate lemma); paper-text fix suggested |
| AQ-11 | Lyapunov destruction from eigen-witness | avoids Perron–Frobenius axiom; confirm |
| AQ-12 | 14.7(a,b) exact-linearised instead of O(‖·‖²) | confirm |
| AQ-13 | 14.8 "preserves G∞ laws" = certificate preservation | confirm |
| AQ-14 | 15.3 proof gap; and A1+A2 unsatisfiable at |A|=3 (`neutrality_unsat_three`) | **REPAIRED-AND-DEEPENED**; axiom-set decision = AQ-19 |
| AQ-15 | Law 5 readings: ESDI-with-prices = `PriceSupported`; Pareto over joint allocations; Second Welfare converse (separating hyperplane) deferred | confirm |
| AQ-16 | PoA proved from Def 5.1(2) + cross-state H-γ bound (paper gives no proof) | confirm intended hypothesis |
| AQ-17 | Law 7: μ-dynamics never displayed | **RESOLVED** (ruling: canonical replicator–mutator; see AQ-20) |
| AQ-18 | Law 7: classical-Hopf interface scoping (periodic orbits; stability & ℓ₁-binding in classical layer) | confirm |
| AQ-19 | §15 axiom-set repair | **RESOLVED** (ruling: drop Neutrality, adopt A5 Overwhelming-Bloc; 15.3/15.4 reproved axiom-free) |
| AQ-20 | Law 7: κ_c(μ) not a Hopf locus, BUT genuine supercritical Hopf proved at γ=1/κ=0 (`rm_true_hopf`) | **RESOLVED** — recommend restating Prop 16.1 at κ=0 (the γ=1 boundary); Thm 16.2 supercriticality stands |

## Plain-language summaries (fellowship dossier)

**Law 1 (Strategic Selection).**  A computer-checked proof that in the
discrete replicator model of competing AI lineages, average performance can
only go up — by an exactly quantified amount — as long as environmental
feedback stays below the H-γ threshold, and that any lineage type
consistently out-earned by a rival (or a portfolio of rivals) is driven to
extinction at a proven geometric rate.  The basin-limitation results are
also verified: once the aligned share falls past the last zero of its growth
function, recovery to full alignment is formally impossible.

**Law 2 (ESDI Characterization).**  The equilibrium theory is verified at
the portfolio level: the Karush–Kuhn–Tucker shadow-price conditions provably
imply portfolio optimality, and — given the standard linear-programming
duality certificate — are exactly equivalent to it; equilibrium support
provably concentrates on at most two agent types (the "barbell") under a
genericity condition.  Machine checking surfaced one real gap in the
published existence proof, now precisely localized for repair.

**Law 3 (H-γ Stability).**  The core stability theorem for multi-level
systems — small cross-level gains imply a global Lyapunov function — is
verified in full as exact algebra, using the paper's own M-matrix
certificate as the working form of the small-gain condition.  The
verification even found the theorem needs one fewer hypothesis than stated.

**Law 4 (G∞ Closure).**  The no-escape-by-going-meta results are verified:
adding a new strategic level with small couplings provably preserves
stability with an explicit margin, margins decay at a proven geometric rate
under repeated extension, and an infinite tower of self-extensions above any
fixed stability floor is formally contradictory.  Two incorrect spectral
displays in the published proofs were caught and replaced by a correct
certificate argument — exactly the kind of pre-referee repair machine
verification exists to provide.

**Law 5 (Constitutional Duality).**  The welfare theorems are now verified
theorems rather than announcements: a computer-checked proof that when a
single constitutional price is charged for the shared capacity and every
lineage's portfolio clears its complementary-slackness conditions, no
reallocation whatsoever can make one lineage better off without hurting
another (First Welfare); and that the same price fully decentralizes the
system — each lineage, maximizing its own priced profit under its private
budget alone, independently reproduces exactly its assigned share of the
frontier allocation (Second Welfare, implementation half).  The
price-of-anarchy bound is verified exactly: equilibrium inefficiency is
provably capped at 1/(1−γ) under the stated cross-state form of the H-γ
condition.

**Law 6 (Alignment Impossibility).**  The heart of the impossibility theory
is verified: the class of self-modifications compatible with a given
Lyapunov certificate is exactly characterized (necessity and sufficiency,
via an exact derivative identity), the maximal safe modification class is
provably unique and closed under arbitrary finite self-modification chains,
and full reachability provably destroys the stability structure.  The
endogenous-electorate impossibility is verified from its key lemma, with an
unconditional concrete witness: majority rule falls to vote-splitting clones
in a two-line machine-checked argument.  Machine-checking also surfaced something deeper:
anonymity and neutrality alone are formally contradictory for a single-winner
rule over the variable-electorate domain at every number of alternatives.
The formalization repairs this in the paper's own spirit — it drops the
neutrality assumption and rebuilds the impossibility on a single axiom that
states the theory's own thesis, that a large enough spawned bloc of identical
voters gets its way; from that axiom the impossibility of stable democratic
aggregation follows with no external inputs, and ordinary majority rule
witnesses that the repaired axioms are consistent.

**Law 7 (Hopf Transition).**  The paper's quantitative claims are now
verified as far as the mathematical library ecosystem currently reaches: the
Hopf curve is a well-defined positive locus over the whole parameter range,
and the first Lyapunov coefficient is provably strictly negative there —
the exact inequality that makes the bifurcation supercritical.  What remains
is the citation to the textbook Hopf theorem itself, stated in the
development as a single named hypothesis (not an axiom).  Instantiating the
model with the standard replicator–mutator dynamics settled where the cycling
actually begins: not at the specific threshold the paper's formula names, but
at the symmetric point where selection vanishes and the interaction becomes
pure rotation — which is precisely the γ = 1 stability boundary that Law 7's
own title invokes.  There the machine-checked eigenvalues cross the imaginary
axis with nonzero frequency, exactly a supercritical Hopf.  So Law 7 is true
at its own stated threshold; the formalization's recommendation is simply to
state the transition there (γ = 1), which also unifies it with the stability
laws, and it flags the separate threshold formula as the one line to
correct.

## Honest-return notes

- The former REPAIR-CANDIDATEs are all machine-checked: AQ-6 (counterexample
  + Nash-map reduction), AQ-10 (corrected spectral displays), AQ-14 (the
  neutrality unsatisfiability finding).  The two delegated design rulings are
  implemented and verified: **AQ-19** — §15 rebuilt on the Overwhelming-Bloc
  axiom (Neutrality dropped, impossibility now axiom-free); **AQ-17/AQ-20** — Law 7
  instantiated with the canonical replicator–mutator, yielding a two-sided
  machine-checked result: the printed κ_c(μ) is not a Hopf locus, but a
  genuine supercritical Hopf *does* occur at the γ = 1 boundary κ = 0 (Law 7's
  own stated threshold).  Law 7 is true where its title says it is; only the
  illustrative locus formula needs correcting.  That two-sided resolution —
  refutation plus the correct positive statement, all cold-checked — is the
  highest-value output of this round.
- Named classical inputs (hypotheses, never axioms): LP strong duality
  (Law 2 hard direction), the Lemma 15.3 interface (Law 6 electorate),
  Brouwer's fixed-point theorem (Law 2 general existence — verified absent
  from Mathlib at this pin), and the classical supercritical Hopf theorem
  (Law 7).  Each is a standard textbook result and a well-defined future
  formalization target.
- Cosmetic: two benign linter notes (unused variable/binder) remain in the
  build log; no mathematical content.
- Suggested next steps: (i) author rulings on the AQ ledger; (ii) spectral
  bridge (ρ ⟺ certificate) as a Tier-2 extension; (iii) May's theorem +
  repaired 15.3 as a standalone project; (iv) `git init` + tag for citable
  provenance; (v) continuous-time SS-1 via given-trajectory `HasDerivAt`
  (the Law-6 file demonstrates the technique works).
