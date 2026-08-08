# RETURN.md — Strategic Evolution Lean kernel, verification return

Originated 2026-07-10; **current as of 2026-08-07** (post-fix-wave — see
[`FIXES.md`](FIXES.md)).  Source: Kevin Vallier, *The Theory of Strategic
Evolution* (arXiv:2512.07901).  Contract: `STATEMENTS.md`.  Prior-work record:
`RECONCILIATION.md` (author ruling 2026-07-10: reconstruct from scratch).

## Headline

**All Seven Laws carry machine-verified content, cold, with zero custom
axioms** — every audited theorem depends on exactly
`{propext, Classical.choice, Quot.sound}` (Lean/Mathlib's standard base;
`admissible_foldr` needs no axioms at all, as do five further theorems outside
the headline list).  No `sorry`, no `admit`, no `native_decide`, no custom
`axiom` anywhere — verified exhaustively over the elaborated environment, not
merely over a curated name list.  This strictly improves the axiom hygiene of
the prior (other-machine) formalization, which the paper's own notes describe
as proven "modulo" ODE-derivative / Perron–Frobenius / spectral-theory axioms.

Read the next section before quoting any of this: zero custom axioms is a
statement about what is *assumed inside Lean*, not a claim that every law is
unconditional.

**141 audited headline theorems; 240 theorems in the elaborated environment;
203 `theorem`/`lemma` declarations in source (190 + 13); 5,435 lines of Lean
across 14 modules.**  The three REPAIR-CANDIDATEs (AQ-6, AQ-10, AQ-14) each
carry machine-checked repair content (see the Repairs section below).

> **Superseded numbers.**  Earlier revisions of this document reported "73
> audited theorems, 2,759 lines across eight modules."  That was a snapshot of
> commit `1bd2b39` (2026-07-10) — and the "73" was the *length of the
> `AxiomsAudit.lean` list* at that commit, never a theorem count (that commit
> already contained 95 theorems).  Four modules have landed since.  Do not
> quote any frozen figure from this file; regenerate with the commands below.

## What is proven, and what is assumed — at a glance

Zero custom axioms means **nothing is assumed inside Lean**.  It does not mean
every law is unconditional: several classical results are carried as explicit
*hypotheses* of the theorems that use them, so a reader can see exactly what is
being taken on faith.  No total is quoted — the inputs are of different kinds
(classical theorems in some laws, modelling axioms in others), so any single
count is ambiguous.  Read the rows:

| Law | Proven outright | Carried as a hypothesis |
|---|---|---|
| 1 — Strategic Selection | SS-1 Lyapunov gain, SS-2 elimination (geometric decay), basin limitation — discrete-time form | hull-domination interface for `frontier_support` (concrete, satisfiable) |
| 2 — ESDI | KKT ⟹ LP optimality; sparsity/barbell; existence in the state-*independent* case; a machine-checked counterexample to the paper's published existence *method* | LP strong duality (zero-gap dual witness) for LP ⟹ KKT; Brouwer for general existence |
| 3 — H-γ Stability | G1 weighted Lyapunov inequality; **certificate ⟺ ρ(Γ) < 1, both directions**, no Perron–Frobenius | — (AQ-9 closed 2026-08-07) |
| 4 — G∞ Closure | certificate extension with explicit margin; slack budget; safe stack depth; no infinite regress | — |
| 5 — Constitutional Duality | First Welfare; Second Welfare *implementation* half; PoA ≤ 1/(1−γ) | cross-state H-γ bound (AQ-16); Second Welfare **converse is absent** (separating hyperplane) |
| 6 — Alignment Impossibility | exact derivative identity, MSG necessity/sufficiency/maximality; reachability destroys Lyapunov structure; anonymity+neutrality unsatisfiable at every \|A\| ≥ 2; majority-rule witness | the Perron–Frobenius step, as the eigen-witness `(u ≥ 0, λ ≥ 1)` in `lyapunov_destruction`; the Law 3 spectral closure does **not** discharge it. The electorate result carries no classical input — the repaired route takes **A5 Overwhelming-Bloc** (a modelling axiom, consistent by the majority-rule witness) and *derives* spawn-manipulability |
| 7 — Hopf Transition | `ell1At` machine-derived from the field (**ℓ₁ = −6μ**); every side condition of `rm_supercritical_hopf`; the degenerate centre at κ = μ = 0; refutation of the paper's printed locus | **the classical planar Hopf theorem** (`ClassicalHopfStatement`) — the single undischarged input |

**Not formalized anywhere**: the identification of the paper's `γ` with any
quantity in the Law 7 model.  Law 7's verified content is stated in the bias
parameter κ.  See the Law 7 section.

## Verification protocol (fence 4)

Figures below are from the 2026-08-07 post-fix-wave state, re-derived from a
clean checkout.

1. **Standalone cold build** (from scratch): fresh clone of Mathlib pinned to
   `5352afccd6866369be9de43f5b7ec47203555f44`, toolchain
   `leanprover/lean4:v4.28.0-rc1`, official olean cache, then
   `lake build` → **`Build completed successfully (7904 jobs)`**, exit 0,
   ≈1 m 34 s wall (after `lake exe cache get`; ≈60 s).
2. **Headline audit**: `lake env lean AxiomsAudit.lean` → exit 0; **141**
   declarations audited — **140** report
   `[propext, Classical.choice, Quot.sound]` and `admissible_foldr` reports
   "does not depend on any axioms".
3. **Exhaustive environment sweep** (the real check — `collectAxioms` over
   every theorem in the `SEKernel` namespace, not a curated name list):
   **240 theorems, 0 axiom declarations, 0 theorems with any nonstandard
   axiom dependency, 0 `sorryAx`.**  Six theorems need no axioms at all
   (`admissible_id/comp/contains/foldr`, `boolTop_rich`, `boolPref.eq_1`);
   one of those six is in the audited headline list.
4. **Anti-vacuity certificates**: `lake env lean RepairProbe.lean` → exit 0.
5. **Zero axiom declarations**, directly checkable:
   `grep -rnE "^[[:space:]]*axiom[[:space:]]" --include='*.lean' .` → no
   matches.  (An unanchored `grep -rn axiom` also matches the word in prose
   and the `#print axioms` directives; those are documentation and audit
   commands, not declarations.)
6. Reproduce with:
   `git clone https://github.com/selfreferencing/TSE_Formal && cd TSE_Formal
   && lake exe cache get && lake build && lake env lean AxiomsAudit.lean`.

### Artifact hashes (sha256)

Recomputed against the **2026-08-07 post-fix-wave state** — the commit that
deletes `legacy/`, adds `Law3_SpectralClosure.lean`, `Law7_Instantiation.lean`
and `RepairProbe.lean`, and rewrites the Law 7 interface.  Earlier revisions
of this table described the 2026-07-10 snapshot; two entries (`SEKernel.lean`,
`AxiomsAudit.lean`) had drifted because those aggregator files grew when the
post-July modules landed.

```
32aab5aa9145106f36ce1852b3a0fdee19514fae8c7a7bde058729c9bff81125  lakefile.toml
53382cbe9b2e717af378843459403242cc24a3cc00865ffc644e7cd420a0f815  lean-toolchain
e0af29a4a8263d83e4c77ffb28031ca743d3944b56563ef72527fcf8c03d62f5  SEKernel.lean
485b0654908e3653c0a9481a3f3833e117768c969fdcc7648c8470c7594bfad6  AxiomsAudit.lean
ded8bd3380c3c54b11bc44db14d68637b6dbab8173cf27c2c232008902cdefa1  RepairProbe.lean
5b8cedb1a1aac9f9c38d8d79d5152b64311e25838d13deb7db1203bea2fbb94e  SEKernel/Law1_Selection.lean
dc9e9960143cbd87ee48ae52f8371449a2c5185e583ccf38358331002e6c62b9  SEKernel/Law2_ESDI.lean
73317191c7a7c00b5ebb233e2027b7dce1b3e1f1d64d6bf8ebb87ae835afe44c  SEKernel/Law3_SpectralClosure.lean
c31503c8258a61ae2c22fff3f7a82c322ff36a0d5c0e830b8b37ac421992528e  SEKernel/Law3_Stability.lean
d418138490a02f57fe17426fa377c207f8335b0b093840ff25326b54919979e7  SEKernel/Law4_ClosureG.lean
cc4a3913478078ec746deface5d93d44db405cbd29179db8e83dda800836137d  SEKernel/Law5_Duality.lean
255f08f816d08d87ebb5a111a984bad9ad13c6f0c5ffb60c4e6b538d90d16919  SEKernel/Law6_Alignment.lean
539439298129f36f769bb1898bc745edec4e3d0d3359129e87b207dd824952ac  SEKernel/Law7_Hopf.lean
67f701463313122503cd606743d7b5e4d0dc860dd81a7ccb4c9415321045de54  SEKernel/Law7_Instantiation.lean
dab1a47708c55f34ee6b1e52a1813764ce0e2b85f373666808d4395e18151213  SEKernel/PriceMarket.lean
d64c9090e08d138f6f56a622fc96cd2bf90c3187be58ec0594b2ac9febd3eb43  SEKernel/PriceMarketMaster.lean
ef2d1a2b4361e67d4b130868725f0ba668459c37e60fa46983a884bfcd1f2e98  SEKernel/SpawnConflict.lean
a98924a64a403aa2afeac0a6f7ad44876dae61f5a1087bf3748985d028f57738  SEKernel/SpectralBridge.lean
2d5bd6c37998454794578bee9ff406e377558e4a184917e613dd1aa8209e5217  SEKernel/WaterLine.lean
36c8751c1aaa84d7bcd804cffffd1dfe0ffd10f6fb6306cc85ec3625812eee8b  STATEMENTS.md
b5ff4c7ef7c24faa5f9ee3a22e24bcdb08126685b641d9d9076507931b006676  RECONCILIATION.md
e496a67417b5776c19942299e2f7cc8543ad4a8607c63f65573682f69d4e3bc2  FIXES.md
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
  cite the certificate lemma `extension_cert` for the weighted form.
  **Superseded 2026-08-07:** this bullet previously ended "the certificate ⟺ ρ
  equivalence (C.5(2)⟺(3)) remains the one recorded spectral interface (not in
  Mathlib)."  AQ-9 closed that interface — the equivalence is now proved in
  both directions in `Law3_SpectralClosure.lean`, with no Perron–Frobenius.
  Note this is the equivalence for the small-gain matrix; it does **not**
  supply the nonnegative eigenvector with λ ≥ 1 that Law 6 needs (see the Law 6
  row of the at-a-glance table).

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

### Law 3 — H-γ Stability: **FORMALIZED, both forms — AQ-9 CLOSED (2026-08-07)**
`SEKernel/Law3_Stability.lean`, `SEKernel/Law3_SpectralClosure.lean`.
- Working small-gain hypothesis = the paper's own Thm C.5(3) M-matrix
  certificate `∃ v > 0, (I − Γᵀ)v ≥ m·𝟙` (`SmallGainCert`).
- Lem 8.1: `G1_weight_pos` (weights positive); Cor C.3: `of_colSums`
  (column-sum sufficient condition, proved outright).
- Thm 8.2 (G1): `G1_weighted_lyapunov(_nonneg)` — the paper's entire
  displayed chain, verified as exact finite algebra: certificate + H-NL ⟹
  `Σ α_ℓ(Var_ℓ + E_ℓ) ≥ m·Σ Var_ℓ ≥ 0`.
- **Finding:** `β ≥ 0` (Assumption 7.3) is not needed for the G1 inequality.
- **AQ-9 CLOSED — the spectral bridge is now a theorem in BOTH directions**
  (`Law3_SpectralClosure.lean`), with zero custom axioms and **no appeal to
  Perron–Frobenius**:
  - `spectral_bound_of_cert` — certificate with margin `m > 0` ⟹ every
    complex eigenvalue of Γ lies in the disc of radius `1 − m/max v < 1`
    (diagonal similarity `D⁻¹ΓᵀD`, `D = diag v`, turning the certificate's
    column margins into row-sum slack, then the Gershgorin-type bound).
  - `cert_of_spectral` — every eigenvalue inside the unit disc ⟹ a
    positive-margin certificate exists.  Gelfand's formula supplies `N` with
    `‖(Γᵀ)^N‖ < 1` in the L∞ operator norm; the **finite Neumann sum**
    `v = Σ_{k<N} (Γᵀ)^k 𝟙` is then a positive weight vector with margin
    `1 − ‖(Γᵀ)^N‖ > 0` (telescoping).
  - `cert_iff_spectral` — the equivalence: paper Thm C.5 (2) ⟺ (3) for
    nonnegative gain matrices.
  - `G1_weighted_lyapunov_of_spectral` — **Law 3 in the paper's own spectral
    phrasing**: ρ(Γ) < 1 (eigenvalue form) ⟹ the G1 weighted Lyapunov
    inequality.  The previously deferred interface no longer appears.
  - Scope note: this is the certificate ⟺ spectral-radius equivalence only.
    The framework's *stability* claim is the G1 inequality it feeds; no
    dynamical-systems stability theorem is asserted here.
- Still deferred: G2/G3 (Tikhonov, Freidlin–Wentzell — analysis layers, out
  of kernel scope per handoff).

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

### Law 7 — Hopf Transition: **NON-VACUOUS interface + machine-derived ℓ₁ / CONDITIONAL(classical planar Hopf)**
`SEKernel/Law7_Hopf.lean`, `SEKernel/Law7_Instantiation.lean`, `RepairProbe.lean`.

> **2026-08-07 — the previous headline was VACUOUS, and is now repaired.**
> The old `ClassicalHopfStatement` was **machine-checkably false**:
> `HopfFamily` carried `α, ω : ℝ → ℝ` as free fields and `ℓ₁` as a bare
> real, none of them tied to the vector field `V`.  The identically-zero
> field satisfied every hypothesis (with `α κ = κ`, `ω = 1`, `ℓ₁ = −1`)
> while admitting no nonconstant periodic orbit, so
> `hopf_transition_conditional` was an implication with a refutable
> antecedent — true for every family, carrying no information.  A clean
> `#print axioms` cannot detect this: **an axiom report certifies that
> nothing was assumed, not that anything was proved.**
>
> **Repair.**  `HopfFamily` now carries the Jacobian `J` together with the
> proof obligation `hasJac` that it IS the Fréchet derivative of `V` at the
> equilibrium; joint smoothness (`smooth`) and a smooth equilibrium branch
> (`eqSmooth`) exclude the remaining pathologies; the frequency comes from
> pinning the critical linearization to the rotation frame
> (`J κc = rotation ω₀`, `ω₀ > 0`); and `ℓ₁` is a **definition** (`ell1At`)
> computed from the second/third-order jet of the shifted field by
> Guckenheimer–Holmes (3.4.11).  Every datum is now a property of `V`.
> `RepairProbe.lean` certifies that the old attacks fail the repaired
> hypotheses (the zero field cannot satisfy `J κc = rotation ω₀`; every
> linear field has `ell1At = 0`, failing `ℓ₁ < 0`).
> `IsPeriodicOrbit.pushforward` transfers orbits through affine coordinate
> changes so the rotation-frame statement applies in a general frame.
>
> **Positive witness** (`Law7_Instantiation.lean`): for the canonical
> biased-RPS replicator–mutator, `rm_supercritical_hopf` discharges *every*
> side condition — equilibrium branch, true Jacobian, joint smoothness,
> rotation-frame conjugacy, transversal trace crossing, and the sign of the
> machine-derived `ℓ₁`.  **The only undischarged input is
> `ClassicalHopfStatement` itself.**
>
> **ℓ₁ = −6μ, derived not transcribed.**  `ell1_Wc` proves the exact
> identity `ℓ₁ = μ(−t⁴ − 2t² − 9)/4` with `t = √3` (no `t² = 3` reduction
> needed), i.e. `ℓ₁ = −6μ`; `ell1_Wc_neg` gives `ℓ₁ < 0` on μ ∈ (0, 1/3).
> This is a property of the dynamics, unlike the older
> `firstLyapunov_neg`, which is a sign fact about a formula transcribed
> from the paper.  Confirmed three independent ways: `ell1At_testField`
> against a system of known coefficient; an independent symbolic
> re-derivation algebraically identical to the Lean definition including
> the `1/(16ω)` block; and direct numerical ODE integration of the
> Poincaré return map, agreeing to 1.8 × 10⁻⁵.
>
> **`ell1_pureRPS_zero` — the degenerate point.**  At `κ = 0, μ = 0`,
> `ℓ₁ = 0`.  The pure-RPS replicator conserves `x₀x₁x₂`; the barycentre is
> a **centre**, a degenerate Hopf, not a limit-cycle generator.  The
> eigenvalue pair does cross there (`rm_true_hopf`), but crossing is only a
> *necessary* condition.  The genuine generic Hopf lives on `κ = −6μ`,
> μ > 0.  **This supersedes the AQ-20 narrative** that placed "the true
> Hopf" at `κ = 0`.
>
> **Open modeling question (not a theorem).**  Whether `κ = −6μ`
> corresponds to the paper's `γ = 1` is *not* established anywhere in this
> development: γ occurs in the Law 7 sources only in prose, the Law 7
> modules do not import Law 3, and no declaration relates them.  Law 7's
> verified content is stated in κ, not γ.
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
- **AQ-20 — WITHDRAWN 2026-08-07.**  The subsection below is retained as a
  record of a superseded conclusion; **do not cite it.**  `rm_true_hopf`
  verifies only the *necessary* conditions at κ = 0 (trace 0, det > 0,
  transversality).  It is not a supercritical Hopf: `ell1_pureRPS_zero` gives
  ℓ₁ = 0 there, and pure RPS conserves `x₀x₁x₂`, so the barycentre is a
  degenerate **centre**.  The genuine locus is κ = −6μ, μ > 0, with ℓ₁ = −6μ.
  The γ = 1 identification below is prose with no formal support (the Law 7
  modules do not import Law 3; `swirlRatio` is a function of κ alone and
  cannot pick out μ = 0; and its definition `(κ+2)/κ` omits the absolute
  values the Frobenius ratio requires, so it is negative on κ ∈ (−2,0), the
  range containing the entire genuine locus).  Superseded text follows.

- ~~**AQ-20 RESOLVED — the true Hopf is at the γ=1 boundary**~~ (`§TrueHopf`).
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
| AQ-20 | Law 7: κ_c(μ) not a Hopf locus (stands); the claimed replacement Hopf at γ=1/κ=0 | **PARTLY WITHDRAWN 2026-08-07** — the refutation of the printed curve stands (`rm_no_hopf`). The replacement claim does not: κ = μ = 0 has ℓ₁ = 0 (`ell1_pureRPS_zero`), a degenerate centre, and the γ = 1 identification has no formal support. Genuine locus: κ = −6μ, ℓ₁ = −6μ |

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

**Law 7 (Hopf Transition).**  *(Rewritten 2026-08-07; the previous summary
placed the transition at the γ = 1 boundary and is withdrawn.)*  Formalization
settled where the cycling actually begins, and it is not where the paper's
printed formula says.  That formula names a curve at positive bias; the
barycentre linearisation has strictly negative trace everywhere on that range,
so no oscillation can begin there — machine-checked.  The genuine threshold
sits at negative bias, on the locus κ = −6μ.  The quantity governing whether
the emerging cycle is stable was recomputed from the dynamics themselves
rather than carried over from the earlier draft, giving ℓ₁ = −6μ; it is
strictly negative across the range, so the cycle that appears is a stable one.
An independent check confirms the recomputation: at the symmetric point the
new value correctly vanishes, recovering the classical fact that
rock–paper–scissors with no bias circles forever at constant amplitude — a
frictionless orbit rather than a bifurcation.  The earlier value did not
vanish there, which is how the error was found.  What remains assumed is the
textbook Hopf theorem itself, carried as one named hypothesis; every other
condition is machine-checked.  Whether this threshold is the framework's own
γ = 1 boundary is **open** — the two parameters are defined over different
objects and no map between them is established.

## Honest-return notes

- The former REPAIR-CANDIDATEs are all machine-checked: AQ-6 (counterexample
  + Nash-map reduction), AQ-10 (corrected spectral displays), AQ-14 (the
  neutrality unsatisfiability finding).  The two delegated design rulings are
  implemented and verified: **AQ-19** — §15 rebuilt on the Overwhelming-Bloc
  axiom (Neutrality dropped, impossibility now axiom-free); **AQ-17/AQ-20** — Law 7
  instantiated with the canonical replicator–mutator.

  > **Superseded 2026-08-07.**  This bullet previously concluded that "a
  > genuine supercritical Hopf *does* occur at the γ = 1 boundary κ = 0" and
  > that "Law 7 is true where its title says it is."  **That is withdrawn.**
  > The eigenvalue pair does cross at κ = μ = 0, but `ell1_pureRPS_zero` shows
  > ℓ₁ = 0 there: it is a degenerate centre (pure RPS conserves `x₀x₁x₂`), not
  > a supercritical Hopf.  The genuine locus is κ = −6μ for μ > 0.  Separately,
  > the identification of that locus with γ = 1 has **no formal support** — γ
  > appears in the Law 7 sources only in prose, and the Law 7 modules do not
  > import Law 3.  What survives is the refutation of the printed curve
  > (`rm_no_hopf`), which never depended on γ.  See the Law 7 section.

- **Named classical inputs, per law** (hypotheses, never axioms).  No total is
  quoted: Law 6 carries two distinct inputs, so any single count is
  ambiguous.  Read the list.
  - **Law 1** — the hull-domination interface, for `frontier_support`
    (concrete and satisfiable, not vacuous).
  - **Law 2** — LP strong duality, as a zero-gap dual witness, for the
    LP ⟹ KKT direction; **and** Brouwer's fixed-point theorem for general
    (state-dependent) existence, verified absent from Mathlib at this pin.
    The state-*independent* existence case is proved outright.
  - **Law 3** — none.  AQ-9 closed; certificate ⟺ ρ(Γ) < 1 both directions.
  - **Law 4** — none.
  - **Law 5** — the cross-state H-γ bound for `poa_bound` (AQ-16).  Separately,
    only the *implementation half* of the Second Welfare theorem is proved;
    the separating-hyperplane converse is **absent**, not hypothesised.
  - **Law 6** — the Perron–Frobenius step that manufactures a nonnegative
    eigenvector with λ ≥ 1 from ρ(Γ) ≥ 1, carried as the eigen-witness
    hypothesis of `lyapunov_destruction`.  The Law 3 spectral closure does
    **not** discharge it — it proves a different statement.
    **Corrected 2026-08-08:** this entry previously also listed the Lemma 15.3
    interface.  It should not have.  That interface is a hypothesis only of the
    *superseded* `endogenous_electorate_impossibility`; the repaired route
    (`endogenous_electorate_impossibility_repaired`) takes `OverwhelmingBloc`
    (A5) and **derives** `SpawnManipulable` via
    `spawnManipulable_of_overwhelmingBloc`.  A5 is a modelling axiom of the
    theory, witnessed consistent by majority rule — not a classical result.
  - **Law 7** — the classical planar Hopf theorem (`ClassicalHopfStatement`).
    Every other side condition of `rm_supercritical_hopf` is discharged.

  Each is a standard result and a well-defined future formalization target.
- Cosmetic: two benign linter notes (unused variable/binder) remain in the
  build log; no mathematical content.
- Suggested next steps: (i) author rulings on the AQ ledger; (ii) spectral
  bridge (ρ ⟺ certificate) as a Tier-2 extension; (iii) May's theorem +
  repaired 15.3 as a standalone project; (iv) `git init` + tag for citable
  provenance; (v) continuous-time SS-1 via given-trajectory `HasDerivAt`
  (the Law-6 file demonstrates the technique works).
