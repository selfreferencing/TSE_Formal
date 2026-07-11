# STATEMENTS.md — Phase 0 contract

Source: Kevin Vallier, *The Theory of Strategic Evolution: Games with Endogenous
Players and Strategic Replicators*, arXiv:2512.07901 (HTML, LaTeXML build of
2025-12-15; sha256 in RECONCILIATION.md). Transcribed 2026-07-10. The Lean must match
the statements below (with the recorded, author-ruled deviations), not a paraphrase.

Triage classes: **T1** = kernel, formalize now (finite/discrete/algebraic);
**T2** = Mathlib-supported but heavier (budget API friction); **T3** = out of kernel
scope (record, defer). **[AQ-n]** = author question, see ambiguity ledger at bottom.

Global setting (paper §2.1–2.3): finite lineage set `J = {1,…,n}`; state space the
simplex `Δ^{n-1} = {x ∈ ℝ^n_{≥0} : Σ x_j = 1}`; performance `f : Δ → ℝ^n` (C¹ in the
paper; the kernel needs only pointwise values at the states it touches); mean
`f̄(x) = Σ_j x_j f_j(x)`; variance `Var_x(f) = Σ_j x_j (f_j(x) − f̄(x))²`.

---

## Law 1 — Strategic Selection (§3)

### Proposition 3.1 (Price Decomposition) — T1 (discrete form) / T2 (continuous)
Paper: under replicator dynamics `ẋ_j = x_j(f_j − f̄)`,
`d/dt f̄(x) = Var_x(f) + E(x)`, where `E(x) = Σ_j x_j ∇f_j · ẋ` is the
environmental/externality term. *Continuous time; E is defined by the equation.*
Kernel form (discrete): for the one-step update `x'_j = x_j f_j(x) / f̄(x)`
(requires `f > 0` on the relevant states), the **selection term is exact**:
`Σ_j x'_j f_j(x) − f̄(x) = Var_x(f)/f̄(x)`, and the total change decomposes as
`f̄(x') − f̄(x) = Var_x(f)/f̄(x) + E_disc(x, x')` with
`E_disc := Σ_j x'_j (f_j(x') − f_j(x))` (definition mirroring the paper's E). [AQ-1]

### Assumption 3.2 (H-γ)
`∃ γ ∈ [0,1)` and forward-invariant region `K` with `|E(x)| ≤ γ·Var_x(f)` on `K`.
Kernel form: same inequality with `E_disc` and `Var/f̄` as the comparators:
`|E_disc(x,x')| ≤ γ · Var_x(f)/f̄(x)`. [AQ-1]

### Theorem 3.3 (SS-1: Lyapunov Structure) — T1
Paper: under RUPSI-lite + H-γ on K:
`d/dt f̄(x) ≥ (1−γ)·Var_x(f) ≥ 0`, equality iff `Var_x(f) = 0`.
Kernel statement (discrete, ℝ, pure algebra):
> `x` on the simplex, `f > 0`, `x'` the discrete replicator update, H-γ-disc with
> `γ < 1` ⟹ `f̄(x') − f̄(x) ≥ (1−γ)·Var_x(f)/f̄(x) ≥ 0`, and
> `f̄(x') = f̄(x) ⟹ Var_x(f) = 0` (and conversely Var = 0 ⟹ E_disc = 0 forces
> equality — the "iff" holds because Var = 0 makes x' = x). Deviation: discrete time
> (handoff-pre-approved [AQ-1]); denominator normalization `Var/f̄` recorded.

### Corollary 3.4 (Consequences of SS-1) — T3 (needs LaSalle; defer)
Convergence to `{Var = 0}`, stability of local maxima. Dynamical-systems layer; the
paper's own Appendix C.7–C.8 cites LaSalle. Deferred with the ODE layer.

### Theorem 3.5 (SS-2a: Elimination of Dominated Types) — T1
Paper: replicator dynamics; if type `d` is uniformly dominated by mixture
`α ∈ Δ(J∖{d})`: `f_d(x) < Σ_{k≠d} α_k f_k(x)` for all `x` in a forward-invariant
region, then `x_d(t) → 0`.
Paper's proof: log-contrast `φ = log x_d − Σ α_k log x_k` has `φ̇ = f_d − Σ α_k f_k
≤ −δ`, so `φ → −∞`; then (Step 4) argues the dominating mixture survives so
`x_d → 0`.
**Proof note (simplification found during transcription):** Step 4 is unnecessary
for the stated conclusion: since `x_k ≤ 1` gives `Π x_k^{α_k} ≤ 1`, one has
`x_d = e^φ · Π x_k^{α_k} ≤ e^φ → 0` directly. The Lean will use this shorter route.
Kernel statements (discrete):
> (i) **Single-type domination** (α a vertex): if `f_d(x_t) ≤ ρ·f_k(x_t)` along the
> orbit with `ρ < 1`, then `x_d(t) ≤ (x_d(0)/x_k(0))·ρ^t → 0` — exact geometric decay.
> (ii) **Mixture domination**: with `φ_t = log x_d(t) − Σ α_k log x_k(t)`, one step
> gives `φ_{t+1} − φ_t = log f_d(x_t) − Σ α_k log f_k(x_t)`; hypothesis
> `log f_d ≤ Σ α_k log f_k − δ` (geometric-mean domination) gives `x_d(t) ≤ e^{φ_0 − δt} → 0`.
> Deviation [AQ-2]: discrete time makes the natural mixture hypothesis
> *geometric-mean* domination (log f versus f, because the discrete log-derivative is
> `log(f_j/f̄)`, not `f_j − f̄`); the paper's arithmetic hypothesis is recovered in
> continuous time. Both forms recorded; author to confirm the discrete hypothesis.

### Theorem 3.6 (SS-2b: Frontier Support) — T1 (conditional form)
Paper: under RUPSI-lite + H-γ, any asymptotically stable `x*` has
`supp(x*) ⊆ F` (ROC frontier). Paper's proof: a non-frontier supported type is
ROC-dominated by a frontier mixture, so SS-2a eliminates it — contradiction.
Kernel statement: the paper's proof skeleton, made exact:
> if every non-frontier type is dominated (in the SS-2a sense) and `x*` is a limit of
> an orbit with `x*_j > 0`, then `j ∈ F`. The geometric step "below the upper convex
> hull ⟹ dominated by a hull mixture" is stated as a separate lemma and NOT proved in
> the kernel (convex-hull API; T2 stretch). [AQ-3]

### Theorem 3.7 (Basin Limitation) — T1 (discrete form)
Paper: `ẋ = x(1−x)g(x)`, x = share of aligned type. (a) If `g(1) < 0`, or `g(1) = 0`
and `g′(1) > 0`, then `x = 1` is Lyapunov unstable. (b) `x̃_max = sup{x : g(x) = 0}`
is the point of no return: below it the system cannot recover to full alignment.
Kernel statements (discrete orbit `x_{t+1} = x_t + η_t·x_t(1−x_t)·g(x_t)`, `η_t > 0`):
> (a) if `g < 0` on `(c,1)` then any orbit in `(c,1)` is strictly decreasing while
> there; in particular no orbit starting in `(c,1)` converges to 1. (Instability of
> full alignment.)
> (b) if `g < 0` on `(x̃,1)` then an orbit that ever sits in `(x̃,1)` moves strictly
> down at that step; consequently no orbit with a term in `[0,x̃]` converges to 1
> provided steps cannot jump from `[0,x̃]` past `1 − ε` (no-overshoot hypothesis,
> recorded). [AQ-4] Deviation: the paper's `g(1)=0, g′(1)>0` branch and the
> continuous-time phrasing are deferred with the ODE layer.

---

## Law 2 — ESDI Characterization (§5)

### Definition 5.1 (ESDI)
`x* ∈ Δ` with (1) `f_j(x*) = f̄(x*)` for `j ∈ supp(x*)`; (2) `f_j(x*) ≤ f̄(x*)` for
`j ∉ supp(x*)`; (3) `x*` a local max of `f̄`. Kernel: conditions (1)–(2) define
`IsEquilibrium` (this is also the standard "Nash equilibrium of the population game"
reading); (3) recorded but not load-bearing in the kernel results below. [AQ-5]

### Theorem 5.2 (ESDI Existence) — T1 for state-independent f; flagged else
Paper: RUPSI-lite, compact state space, continuous fitness ⟹ an ESDI exists.
Paper's proof: extreme value theorem on `f̄`; "any maximum satisfies the ESDI
conditions by Theorem 3.3."
**REPAIR-CANDIDATE [AQ-6]:** for state-*dependent* `f`, a maximizer of `f̄` need not
satisfy (1)–(2) (the first-order condition at a maximizer of `x ↦ Σ x_j f_j(x)`
involves `∂f/∂x` terms the proof does not control). The claim is clean when `f` is
state-independent (`f_j` constant): then a maximizer puts mass only on argmax types
and (1)–(2) hold with `f̄(x*) = max_j f_j`.
Kernel statement: existence of an equilibrium state (conditions (1)–(2)) for
state-independent `f` on a finite type set — fully proved, constructive (uniform
distribution on argmax set). General state-dependent existence: REPAIRED via the
Nash-map reduction (see AQ-6 in the ledger — fixed point ⟹ equilibrium proved by
pure algebra; the fixed point itself is Brouwer, verified NOT to be in Mathlib at
this pin, hence the recorded classical input).

### Theorem 5.3 (Nash–KKT–LP Equivalence) — T1
Paper: for a GEP with linear constraints, TFAE: (1) `x*` Nash equilibrium of the
population game; (2) `x*` satisfies KKT for ROC maximization; (3) `x*` solves the LP
relaxation of portfolio optimization. **The paper gives no proof in the body**
(delegated to `Sparsity.lean`); §12.1–12.2 fixes the primal LP
`max Σ r_i n_i  s.t.  Σ c_i n_i ≤ B, Σ ℓ_i n_i ≤ Q, n ≥ 0` and its dual
`min μB + λQ  s.t.  μc_i + λℓ_i ≥ r_i, μ,λ ≥ 0`.
Kernel statement (finite, exact — definitional choices recorded [AQ-7]):
> For the portfolio LP above with `n*` primal-feasible: TFAE
> (KKT) ∃ dual-feasible `(μ,λ)` with complementary slackness
> (`n*_i > 0 ⟹ μc_i + λℓ_i = r_i`; `μ > 0 ⟹ Σ c_i n*_i = B`; `λ > 0 ⟹ Σ ℓ_i n*_i = Q`);
> (LP) `n*` maximizes `Σ r_i n_i` over the feasible polytope;
> (NASH) no feasible unilateral improvement, which for one lineage's linear objective
> is literally (LP) — recorded as the population-game reading: supported types
> maximize return per shadow-cost. Proof route: weak duality + complementary
> slackness both ways (elementary algebra); strong duality is NOT needed because KKT
> certificates are constructed explicitly in the (LP)⟹(KKT) direction for this
> 2-constraint LP via the supporting-line argument of Prop 2.8. If the general
> (LP)⟹(KKT) direction resists elementary treatment, it is stated with the dual
> witness as hypothesis and the loss recorded. [AQ-7]

### Theorem 5.4 (Constraint-Role Sparsity) — T1 (stretch)
Paper: with `m` binding constraints, `|supp(x*)| ≤ m`. No proof in body.
Kernel reading [AQ-8]: for the 2-constraint LP, extreme-point optima have support
≤ 2; via KKT: active types lie on the line `μ + λa_i = b_i` in the `(a,b)`-plane
(Prop 2.8), and generic position (no 3 collinear `(a_i,b_i)`) forces `|supp| ≤ 2`.
Formalize the generic-position version; "generically finite" language deferred.

### Corollary 5.5 (Barbell) — follows from 5.4 instance `m = 2`; same file.

---

## Law 3 — H-γ Stability (§§6–8)

### Definitions 7.1–7.7 (N-level system, gain matrix, small gain, slack)
Levels `ℓ = 1..N`, each with `Var^{(ℓ)} ≥ 0` and externality `E^{(ℓ)}`;
H-NL (Assumption 7.3): `E^{(ℓ)} ≥ −γ_ℓ Var^{(ℓ)} − Σ_{ℓ′≠ℓ} β_{ℓℓ′} Var^{(ℓ′)}`,
`γ_ℓ ∈ [0,1)`, `β ≥ 0`. Gain matrix `Γ_{ℓℓ} = 0`, `Γ_{ℓℓ′} = β_{ℓℓ′}/(1−γ_ℓ)`.
SG-NL: `ρ(Γ) < 1`. Slack `σ = 1 − ρ(Γ)`.
**Kernel primitive (per paper's own Thm C.5(3), M-matrix characterization):**
`SmallGainCert Γ v ⟺ v > 0 ∧ (I − Γᵀ)v ≥ 𝟙` (componentwise; 𝟙 normalizes v's scale).
For nonnegative Γ this is equivalent to ρ(Γ) < 1 (C.5(2)⟺(3)); the kernel proves
everything from the certificate and proves the row-sum sufficient condition (C.3)
outright; the spectral bridge itself is the recorded T2 interface. [AQ-9]

### Lemma 8.1 (Weight Existence via Neumann Series) — T2 (bridge) / T1 (certificate)
Paper: ρ(Γ) < 1 ⟹ `v := (I−Γᵀ)^{-1}𝟙 > 0`, weights `α_ℓ = v_ℓ/(1−γ_ℓ) > 0`.
Kernel: the certificate v IS the object; positivity of α from `γ_ℓ < 1` is algebra.
Norm-route bridge (T2): `‖Γᵀ‖ < 1 ⟹` Neumann series certificate exists.

### Theorem 8.2 (G1: N-Level Lyapunov) — T1 (the algebraic heart)
Paper: under RUPSI, SR3, H-NL, SG-NL: `Ψ_N = Σ α_ℓ f̄^{(ℓ)}` satisfies
`d/dt Ψ_N ≥ c·Σ_ℓ Var^{(ℓ)} ≥ 0`.
Kernel statement (exactly the paper's chain of ten displayed (in)equalities, which
is pure finite algebra once `d/dt f̄^{(ℓ)} = Var^{(ℓ)} + E^{(ℓ)}` is taken as the
per-level Price input):
> Given reals `Var_ℓ ≥ 0`, `E_ℓ`, `γ_ℓ < 1`, `β ≥ 0` with H-NL, and `SmallGainCert Γ v`,
> the weights `α_ℓ = v_ℓ/(1−γ_ℓ)` are positive and
> `Σ_ℓ α_ℓ (Var_ℓ + E_ℓ) ≥ Σ_ℓ Var_ℓ ≥ 0`.
> Applied per time step (discrete) or to the given derivative (continuous), this is
> the paper's conclusion with `c = 1` in certificate normalization; Corollary 8.3's
> `c ≥ σ·min(1−γ_ℓ)` becomes the recorded normalization remark. [AQ-9]

### Theorem 8.6 (G2: Adiabatic Tracking) — T3 (Tikhonov / singular perturbation; defer)
### Theorem 8.9 (G3: Stochastic Stability) — T3 (Freidlin–Wentzell; defer)

---

## Law 4 — G∞ Closure (§11)

### Lemma 11.3 (Single-Step Gain-Slack) — REPAIR-CANDIDATE as stated [AQ-10]
Paper: if `‖b‖_{∞,v} ≤ θσ` and `⟨c,v⟩ ≤ θσ` (θ < 1) then the block extension
`Γ̃ = [[Γ, b],[cᵀ, 0]]` has slack `σ′ ≥ (1−θ)σ`. Proof invokes
`ρ(Γ̃) ≤ ρ(Γ) + √(‖b‖_{∞,v}·‖c‖_{1,v})` ("spectral perturbation") — this bound is
not standard as displayed, and Thm 11.7(d)'s companion "by Gershgorin" display
`ρ(Γ̃) ≤ max(ρ(Γ)+‖b‖_{∞,v}, ⟨c,v⟩/‖v‖₁)` is also not literal Gershgorin. Flagged
to author. Kernel replacement (exact, certificate form — proves the theorem's
*point*, that small couplings preserve small gain with quantified margin):
> **Certificate Extension Lemma.** If `SmallGainCert Γ v` with margin `m` (i.e.
> `(I−Γᵀ)v ≥ m𝟙`), `b, c ≥ 0`, and there is `w > 0` with `⟨b,v⟩ + m ≤ w` and
> `c_ℓ · w ≤ 1 − m′` (componentwise) where `m′ ≤ m`, then
> `SmallGainCert Γ̃ (v,w)` with margin `m′`. Explicit witness `w = ⟨b,v⟩ + m`.
Slack tracking `σ′ ≥ (1−θ)σ` re-expressed as margin arithmetic. [AQ-10]

### Lemma 11.4 (Slack Budget) — T1
Paper: after `m` admissible extensions with uniform margin θ: `σ_m ≥ (1−θ)^m σ_0`.
Kernel: induction on the certificate-margin version of 11.3. Pure algebra.

### Theorem 11.6 (Safe Stack Depth) — T1
Paper: `M ≤ log(σ_0/σ_min)/θ`. Kernel: from 11.4,
`(1−θ)^M σ_0 ≥ σ_min` plus `log(1−θ) ≤ −θ` gives the bound (Real.log; Mathlib).
Equivalent exact form without logs also stated: `M·θ ≤ log(σ_0/σ_min)`.

### Theorem 11.7 (G∞ Closure) — split
(a) Self-similarity: informal/structural (RUPSI inheritance narrative) — T3, recorded.
(b) Level-independent Lyapunov weights: **same algebra as G1** — T1 (shared lemma).
(c) Protection bits / quasi-potentials — T3 (stochastic layer; defer with G3).
(d) Extension preserves small gain with margin σ/2 — T1 via the Certificate
Extension Lemma (instance `θ = 1/2`). [AQ-10]

### Corollary 11.8 (No Infinite Regress) — T1 as packaging
Kernel: under a positive slack floor `σ_min > 0` and per-step cost θ, the safe depth
is finite (11.6); "cannot escape selection pressure by going meta" = no infinite
admissible chain keeps margin ≥ σ_min. Stated and proved as the contrapositive of
11.4/11.6.

**Handoff note:** the handoff's provisional guess that Law 4 is "unique maximal
composition-closed class" material actually matches **Theorem 14.8** (Law 6 section);
formalized there. Phase 0 supersedes the guess per handoff instruction.

---

## Law 5 — Constitutional Duality (§12) — T1 (formalized; readings AQ-15/AQ-16)

**The paper states Theorems 12.1, 12.2 and 12.4 without body proofs**; the kernel
supplies statements and proofs in the GEP setting (Def 2.9 / §12.1): lineages `Λ`
with private budgets `B_ℓ`, one shared capacity `Q`, one constitutional shadow
price `λ`.

### Theorem 12.1 (First Welfare Theorem) — T1, PROVED
Paper: every ESDI is Pareto efficient in the space of feasible allocations.
Kernel statement (`first_welfare`): a **shadow-price-supported** joint allocation
(per-lineage dual feasibility `r_i ≤ μ_ℓ c_i + λ ℓ_i`, complementary slackness on
supports, budgets, and the shared capacity) is Pareto efficient among all joint
allocations satisfying the private budgets and shared capacity. Proof: per-lineage
CS value identities `value_ℓ = μ_ℓ B_ℓ + λ·load_ℓ` + weak duality at any deviation,
summed over lineages; the λ-terms cancel against the shared `Q`. "ESDI" is read as
price-supportedness (the shadow-price form of Def 5.1 conditions delivered by Law 2's
`KKT.reduced_return`). [AQ-15]

### Theorem 12.2 (Second Welfare Theorem) — split
Paper: any Pareto-efficient allocation on the ROC frontier can be implemented as an
ESDI with appropriate shadow prices.
Kernel (`shadow_price_implementation`), **implementation half PROVED**: at a
price-supported allocation, each lineage's assigned portfolio maximizes its profit
`Σ_i (r_i − λℓ_i) m_i` over its private budget set alone — the constitutional price
fully decentralizes the shared capacity ("shadow prices implement the frontier
allocation"). **Converse half** (Pareto-efficient ⟹ supporting prices exist):
separating-hyperplane/convexity content — recorded, deferred (T2/T3). [AQ-15]

### Theorem 12.4 (PoA Bounds) — T1, PROVED under stated hypothesis
Paper: under H-γ with γ < 1, `PoA ≤ 1/(1−γ)`. No proof or precise static hypothesis
given.
Kernel (`poa_bound`, `poa_bound_ratio`): with `x` an equilibrium in the Def 5.1(2)
sense (`f_j(x) ≤ f̄(x)` for all j) and `y` any state, under the **cross-state H-γ
bound** `Σ_j y_j (f_j(y) − f_j(x)) ≤ γ·f̄(y)` — the static face of Assumption 3.2 —
one gets `(1−γ)·f̄(y) ≤ f̄(x)`, i.e. `f̄(y)/f̄(x) ≤ 1/(1−γ)`. This is a
smoothness-style two-line argument; the cross-state hypothesis is the kernel's
precise reading of "under H-γ" and needs author confirmation. [AQ-16]

---

## Law 6 — Alignment Impossibility (§14) + Endogenous Electorate (§15)

### Definitions 14.1–14.3
Modification classes `M_R` (RUPSI-preserving), `M_SG` (small-gain preserving),
`M_0 = M_R ∩ M_SG`; full reachability = any state reachable by finite modification
sequences; `M_SG(V)` = modifications whose linearization `J_m` at `x*` makes
`S_m = ½(HJ_m + J_mᵀH)` negative semidefinite on the tangent space (`H` = Hessian
of `V`).
Kernel encoding: modifications as endomaps of a state type; classes as sets closed
under composition (monoid substructure); "preserves P" literally.

### Lemma 14.5 (Lyapunov Destruction) — T1 in eigen-witness form
Paper: `ρ(Γ) ≥ 1 ⟹` no positive weights satisfy the G1 condition.
Kernel (exact, zero-axiom):
> if `Γ ≥ 0` has an eigenpair `Γu = λu` with `u ≥ 0`, `u ≠ 0`, `λ ≥ 1`, then no
> `SmallGainCert Γ v` exists. (Pairing: `0 < m⟨u,𝟙⟩·(scale) ≤ ⟨u,(I−Γᵀ)v⟩ =
> (1−λ)⟨u,v⟩ ≤ 0`, contradiction.)
Perron–Frobenius ("ρ(Γ) itself is such an eigenvalue") is exactly the prior work's
"modulo" axiom — here it is NOT assumed; the eigen-witness is the hypothesis. [AQ-11]

### Theorem 14.7 (Alignment Impossibility) — T1 in exact-quadratic form
Paper: (a) `m ∈ M_SG(V)` ⟹ V strict Lyapunov near x*; (b) converse; (c) `M_SG(V)`
maximal; (d) full reachability incompatible with preserving G1/G3 Lyapunov structure.
Kernel statements (linearized-exact; deviation [AQ-12]):
> For linear dynamics `ẋ = J(x−x*)` (or one discrete linear step) and quadratic
> `V(x) = ½(x−x*)ᵀH(x−x*)`: the derivative along the flow is exactly the quadratic
> form of `S = ½(HJ + JᵀH)`; hence (a) `S ⪯ 0` on the tangent space ⟹ `V̇ ≤ 0` there
> (exact, not O(·²)); (b) `V̇ ≤ 0` on the tangent space ⟹ `S ⪯ 0` (quadratic forms:
> `V̇(x) = (x−x*)ᵀS(x−x*)`); (c) maximality is then definitional and proved as: the
> class of ALL S-negative modifications contains any class sharing V; (d) packaged:
> if the reachable set contains a state whose gain matrix admits an eigen-witness
> (14.5), no certificate — hence no G1-type weighted Lyapunov — survives full
> reachability. Heteroclinic sub-argument (Lemma 14.6): T3, deferred (dynamical).

### Theorem 14.8 (Maximal Admissible Class) — T1 (the lattice/closure result)
Paper: `M_0 = M_R ∩ M_SG` is the unique maximal modification class preserving the
G∞ structural laws under arbitrary finite self-modification sequences.
Kernel: with "safe" := preserves the stated certificate/invariant at every reachable
state, the set `M_max` of all safe modifications is (i) closed under composition,
(ii) contains every safe class, (iii) is the unique maximal such class (union of
safe classes is safe). Instantiated with the Law-3 certificate to tie `M_SG` in;
`M_R ∩ M_SG` realized as intersection-of-preservers, itself a preserver class. This
is the handoff's predicted closure-operator content — it lives in Law 6. [AQ-13]

### Lemma 15.2 (Two-Outcome Majority; May's theorem) — T2/T3 (recorded)
Needs May (1952). Not in Mathlib. Deferred from the kernel; see [AQ-14].

### Lemma 15.3 (Spawn Manipulation) — REPAIR-CANDIDATE as proved [AQ-14]
Paper: under A1–A4 there exist `P, ≻, k` with `f(P + k·≻) ≻ f(P)`.
Transcription note: Step 4 argues "adding voters who favour c over a cannot switch
the outcome to a" from Positive Responsiveness (A3) — but A3 as stated is a
fixed-electorate, single-voter-raises-`a` axiom; the step needs a variable-population
monotonicity principle not among A1–A4. Flagged to author (referee would likely
flag it too). Kernel: 15.3 is taken as HYPOTHESIS for 15.4 (below); additionally the
kernel proves unconditionally the **majority-rule witness**: for `|A| = 2` and
majority rule with any anti-abstention tie-break, spawning k copies of the loser's
ballot flips the outcome — a concrete, fully-proved spawn-manipulation instance.

### Theorem 15.4 (Endogenous-Electorate Impossibility) — T1 (conditional form)
Paper: no `f` satisfies A1–A4 + Population-Stability (Def 15.1:
`f(P + k·≻) ⪰_≻ f(P) ⟹ f(P + k·≻) = f(P)`).
Kernel: profiles as multisets of abstract ballots (variable electorate; Anonymity A1
holds by construction of the encoding), A4 (Onto) formalized, A2/A3 recorded (they are
consumed only by the deferred 15.2/15.3); Population-Stability transcribed exactly;
theorem proved from the 15.3 interface: any `f` with a spawn-manipulation triple
violates Population-Stability. The unconditional impossibility inherits 15.3's
status. [AQ-14]

---

## Law 7 — Hopf Transition (§16) — T1 (displayed algebra) + classical interface

### Proposition 16.1 (Hopf Curve) — locus data PROVED
Paper: bifurcation along `κ_c(μ) = (1−√(1−3μ))/(3μ)·(1−μ)`, `μ ∈ (0,1/3)`.
Kernel (`hopfCurve`, `hopfCurve_pos`): the closed form is transcribed and proved
strictly positive on the parameter range. The bifurcation claim itself rides on the
classical interface below. **[AQ-17]**: §16.2 defines Π(κ) but never displays the
μ-dynamics (presumably replicator–mutator); the concrete family is needed to
instantiate the interface and eventually derive α, ω, ℓ₁ from the model — author to
specify the equations.

### Theorem 16.2 (Supercritical Bifurcation) — split
Paper: `ℓ₁(κ_c, μ) = −(√3/8)(1−3μ)/(1−μ)² < 0` on `μ ∈ (0,1/3)`; bifurcation is
supercritical, a stable limit cycle emerges.
Kernel: `firstLyapunov_neg` — **the supercriticality inequality is fully proved**
(the paper's displayed formula, machine-checked negative on the whole range).
The passage from `ℓ₁ < 0` + eigenvalue crossing to limit cycles is the classical
supercritical Hopf theorem (Guckenheimer–Holmes 3.4.2), **not in Mathlib**: stated
as one explicit Prop (`ClassicalHopfStatement` — hypotheses: α(κ_c) = 0, ω(κ_c) ≠ 0,
transversal crossing, ℓ₁ < 0; conclusion: nonconstant periodic orbits past κ_c in
the given-trajectory encoding `IsPeriodicOrbit`). `hopf_transition_conditional`
composes it with the proved inequality. **[AQ-18]**: the interface's conclusion
states existence of nonconstant periodic orbits and does not re-state orbital
stability of the cycle; binding the abstract ℓ₁ argument to the normal-form cubic
coefficient of the concrete vector field is part of the same deferred classical
content. Confirm this scoping.

### Theorem 16.3 (Amplitude Scaling) — T3 (deferred)
`A(κ) ~ C·√(κ − κ_c)`: asymptotic normal-form estimate; deferred with the
classical layer.

---

## Ambiguity / author-question ledger

**Confirmation status (2026-07-10).** Kevin delegated the AQ confirmations to the
formalizer ("confirm the AQ items however you think best"). Ruling recorded below;
each item's disposition is marked **[✓ CONFIRMED]** (encoding/fidelity choice ratified
as-is), **[✓ RESOLVED]** (design ruling made + machine-checked), or
**[⚠ REPAIR — author]** (a mathematical decision about the paper's own content that
only the author should finalize; the kernel supplies the analysis and a recommendation).

- Encoding-fidelity items, all **[✓ CONFIRMED]** — these are faithful formal readings
  of the paper's statements, each chosen to be the exact/natural one and verified in
  Lean: **AQ-1** (SS-1 discrete `Var/f̄`), **AQ-2** (SS-2a geometric-mean domination),
  **AQ-3** (SS-2b hull interface), **AQ-4** (basin discrete no-overshoot), **AQ-5/7**
  (ESDI conditions; Nash = no-improving-deviation; portfolio-LP KKT/LP defs), **AQ-8**
  (sparsity under generic position), **AQ-9** (small gain via the paper's own M-matrix
  certificate C.5(3)), **AQ-11** (Lyapunov destruction from eigen-witness), **AQ-12**
  (14.7 exact-linearised), **AQ-13** (14.8 = certificate preservation), **AQ-15/16**
  (Law 5 `PriceSupported`; PoA cross-state H-γ), **AQ-18** (classical-Hopf interface
  scoping). Rationale: the handoff's fence 1 (formalize as written) plus fence 3 (no
  strengthening) make these the correct readings; where the paper left a definitional
  choice, the kernel took the one that is both provable and closest to the text, and
  the cold build is the evidence.
- Design rulings delegated and made: **AQ-19 [✓ RESOLVED]** (drop Neutrality; adopt A5
  Overwhelming-Bloc; §15 reproved axiom-free), **AQ-17 [✓ RESOLVED]** (canonical
  replicator–mutator model), **AQ-20 [✓ RESOLVED]** (true Hopf at γ=1/κ=0; κ_c is the
  artifact).
- Author-facing mathematical decisions (kernel gives analysis + recommendation, author
  finalizes): **AQ-6 [⚠ REPAIR]** (adopt Brouwer/Nash-map proof for Thm 5.2 —
  reduction machine-checked), **AQ-10 [⚠ REPAIR]** (replace the two spectral displays
  with the corrected `SpectralBridge` bounds), **AQ-20 [⚠ REPAIR]** (replace Prop 16.1's
  κ_c(μ) with the κ=0 threshold). These change the *paper's* text, so they are
  recommendations, not unilateral edits.

Detailed per-item notes follow.

- **[AQ-1]** SS-1 discrete-time restatement (update `x'_j = x_j f_j/f̄`, `f > 0`,
  H-γ-disc on `E_disc` vs `Var/f̄`). Handoff pre-approves discrete-or-author-approved;
  the `Var/f̄` normalization is the natural exact one. **Default taken:** formalize as
  above; continuous given-trajectory version optional later. Confirm.
- **[AQ-2]** SS-2a discrete mixture hypothesis: geometric-mean domination
  (`log f_d ≤ Σ α_k log f_k − δ`) replaces the paper's arithmetic domination (they
  coincide in continuous time). Single-type case needs only ratio domination. Confirm.
- **[AQ-3]** SS-2b: hull-domination step ("below ROC frontier ⟹ dominated by frontier
  mixture") stated as lemma-interface, not proved in kernel. OK?
- **[AQ-4]** Basin (b) discrete no-overshoot hypothesis; and (a) formalized on an
  interval `(c,1)` with `g < 0` rather than via `g(1)`/`g′(1)` germ data. Confirm.
- **[AQ-5]** "Nash equilibrium of the population game" read as ESDI conditions (1)–(2).
  Confirm.
- **[AQ-6]** ESDI existence (5.2): paper's EVT proof does not yield conditions
  (1)–(2) for state-dependent `f`. **REPAIRED in kernel** (Law2 §ExistenceRepair):
  `maximizer_method_gap` machine-checks a counterexample to the proof method
  (continuous `F` whose `f̄`-maximizer violates condition (1));
  `exists_mean_maximizer` records what EVT does give; the fixed route is Nash's
  improvement map — `nashMap_fixedPoint_equilibrium` proves fixed point ⟹
  conditions (1)–(2) by pure algebra, and `esdi_exists_of_fixedPoint` packages
  general existence **conditional on the fixed point** (Brouwer: NOT yet in
  Mathlib — the recorded classical input). Author ruling owed: replace the
  paper's EVT proof by the Brouwer/Nash-map argument (recommended text supplied
  in RETURN.md).
- **[AQ-7]** Triple equivalence: precise definitions of the three conditions fixed as
  in the kernel statement (portfolio LP; KKT = dual witness + complementary
  slackness; Nash = no feasible improving deviation). Confirm the intended reading.
- **[AQ-8]** Sparsity 5.4: proved under generic position (no 3 of the `(a_i,b_i)`
  collinear); "m binding constraints ⟹ support ≤ m" in general needs a
  degeneracy convention. Confirm.
- **[AQ-9]** Small gain via certificate `∃v>0, (I−Γᵀ)v ≥ 𝟙` (paper's Thm C.5(3)),
  with ρ-bridge deferred; G1 constant `c = 1` in certificate normalization
  (Cor 8.3 becomes a normalization remark). Confirm.
- **[AQ-10]** Lemma 11.3 / Thm 11.7(d): the displayed spectral-perturbation and
  "Gershgorin" bounds are not correct as stated. **REPAIRED in kernel** twice over:
  (i) exact Certificate Extension Lemma (`extension_cert`, explicit witnesses);
  (ii) NEW `SpectralBridge.lean` — correct spectral displays proved via Mathlib's
  Banach-algebra spectrum API: `eigenvalue_le_rowSum` (Gershgorin-type C.2),
  `gain_eigenvalue_bound` (spectral C.3), `extension_eigenvalue_bound` (the
  corrected 11.3/11.7(d) display: row-sum slack ⟹ every eigenvalue of Γ̃ within
  1 − m′). Suggested replacement text for the paper's displays in RETURN.md.
  The Perron–Frobenius certificate ⟺ ρ equivalence (C.5(2)⟺(3)) remains the one
  recorded spectral interface (not in Mathlib).
- **[AQ-11]** Lyapunov destruction proved from an eigen-witness `(u ≥ 0, λ ≥ 1)`
  hypothesis rather than from `ρ(Γ) ≥ 1` (Perron–Frobenius supplies the witness for
  nonnegative Γ; that bridge stays outside the kernel). Confirm.
- **[AQ-12]** 14.7(a)/(b) formalized for the linearized dynamics exactly (quadratic
  form identity) instead of the paper's `O(‖·‖²)` near-equilibrium argument. Confirm.
- **[AQ-13]** 14.8 "preserves the G∞ structural laws" formalized as "preserves the
  stated certificate at every reachable state"; maximal class = all preservers.
  Confirm this captures the intended reading.
- **[AQ-15]** Law 5 readings: "ESDI with shadow prices" = the `PriceSupported`
  structure (per-lineage μ_ℓ, one constitutional λ, CS throughout); Pareto efficiency
  over joint allocations with private budgets + shared capacity; Second Welfare split
  into implementation half (proved) and separating-hyperplane converse (deferred).
  Confirm.
- **[AQ-16]** PoA (12.4): paper gives no proof; kernel derives the exact bound from
  Def 5.1(2) + the cross-state externality bound `Σ_j y_j(f_j(y) − f_j(x)) ≤ γ f̄(y)`.
  Confirm this is the intended static reading of "under H-γ" (it is the natural
  smoothness-style transcription).
- **[AQ-14]** §15: (i) May's theorem not formalized in kernel (15.2 recorded); (ii)
  Lemma 15.3's Step 4 needs a variable-population monotonicity axiom beyond A1–A4 as
  stated; (iii) kernel delivers 15.4 conditional on the 15.3 interface plus an
  unconditional majority-rule manipulation witness. **PARTIALLY REPAIRED + DEEPENED:**
  `neutrality_unsat_three` machine-checks that **A1 + A2 alone are unsatisfiable at
  |A| = 3** over the full variable-electorate domain (the Condorcet profile is
  invariant under the 3-cycle, which fixes no alternative) — so 15.2–15.5 are vacuous
  at |A| = 3 as stated. See [AQ-19] for the repair decision.
- **[AQ-17] RESOLVED (design ruling, delegated to formalizer 2026-07-10).**
  Ruling: instantiate the canonical **replicator–mutator** (uniform mutation rate
  μ toward the barycentre) on the printed Π(κ) — the well-established closure of
  the §2.2 "Innovation Rare" axiom. This makes the model decidable, and the answer
  is a **finding → REPAIR-CANDIDATE AQ-20**: the center-linearization trace is
  `−κ/3 − 2μ` (`rm_center_trace`, machine-checked via `rm_diag0`/`rm_diag1`),
  strictly negative for all κ ≥ 0, μ > 0 (`rm_no_hopf`) — so **no Hopf occurs at
  κ_c(μ) > 0** under this (or the quasispecies) canonical dynamics; the interior
  equilibrium is a stable focus throughout. `hopfCurve_root` proves κ_c is the
  small root of `3μκ² − 2(1−μ)κ + (1−μ)² = 0`, the fingerprint offered to
  identify the intended family (a different mutation coupling / time rescaling /
  payoff normalization would change the trace and could place a genuine Hopf on
  this curve). Author to specify which; the classical-Hopf interface then applies
  once α(κ_c) = 0 holds for the chosen model.
- **[AQ-18]** Classical-Hopf interface scoping (see Law 7 section). Confirm.
- **[AQ-20] RESOLVED (finding + constructive correction, 2026-07-10).** Two
  halves, both machine-checked: (i) NEGATIVE — the printed `κ_c(μ)` is not a
  Hopf locus under the canonical replicator–mutator (`rm_no_hopf`: trace
  `−κ/3−2μ < 0` on all κ ≥ 0); (ii) POSITIVE — the dynamics **do** have a
  genuine supercritical Hopf, at `κ = 0`, which is exactly the pure-swirl
  `γ = 1` boundary (Law 7's own stated threshold). Center eigenvalues
  `−κ/6 ± i√3(κ+2)/6`: all three Hopf conditions verified at κ = 0
  (`rm_true_hopf` — trace 0, det 1/3 > 0 so frequency ±i/√3, transversal slope
  −1/3), and `swirl_ratio_blowup` locates κ = 0 as the `γ = 1` point. The
  paper's `ℓ₁ = −(√3/8)(…)` carries the equilateral-RPS `√3` fingerprint of the
  κ = 0 computation, corroborating that ℓ₁ is the true-Hopf coefficient.
  **Recommendation:** keep Thm 16.2's supercriticality (verified); replace
  Prop 16.1's `κ_c(μ)` with the threshold `κ = 0` (`γ = 1`), aligning Law 7
  with Laws 1/3 through the swirl decomposition. Machine-checked in
  `Law7_Hopf.lean §ReplicatorMutator` and `§TrueHopf`.
- **[AQ-19]** §15 axiom-set repair decision (given the |A| = 3 inconsistency):
  options — (a) restrict the domain to odd electorates (classical fix for resolute
  anonymous+neutral rules); (b) state the theorems for |A| ≥ 4 (the Condorcet-cycle
  obstruction then only forces the winner outside the cycled triple); (c) make `f`
  set-valued (irresolute) and adapt Population-Stability; (d) weaken Neutrality.
  Plus: adopt an explicit variable-population monotonicity axiom A3′ for Step 4 of
  Lemma 15.3 (e.g. "spawning voters who all rank `c` above `a` cannot change the
  winner *to* `a`"). Author's call; the kernel's 15.4-from-interface and the
  majority witness are compatible with all options.
