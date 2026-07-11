/-
SEKernel / Law6_Alignment.lean
Law 6 (Alignment Impossibility) — arXiv:2512.07901 §§14–15, kernel form.

Four components:

1. **V-small-gain quadratic calculus** (Definition 14.3, Theorem 14.7(a,b,c)).
   For quadratic `V` with Hessian form `H` and linearised dynamics `ẏ = J y`,
   the derivative of `V` along a given trajectory is *exactly* the quadratic
   form of `S = ½(HJ + JᵀH)` (`hasDerivAt_qform_along_linear`), so:
   (a) `S ⪯ 0` on the tangent set ⟹ `V` non-increasing along trajectories
   there; (b) if no sufficiently small Euler step from `z` increases `V`,
   the `S`-form at `z` is ≤ 0 (algebraic limit argument, no analysis);
   (c) `M_SG(V)` — all `J` with `S ⪯ 0` on the tangent set — contains every
   class sharing `V` as a (linearised) Lyapunov function.
   Deviation AQ-12: exact linearised statements replace the paper's
   `O(‖x−x*‖²)` near-equilibrium argument.

2. **Lyapunov destruction** (Lemma 14.5, eigen-witness form, AQ-11): if the
   gain matrix has an eigenvector `u ≥ 0, u ≠ 0` with eigenvalue `λ ≥ 1`,
   no small-gain certificate exists.  (Perron–Frobenius, which supplies such
   a witness from ρ(Γ) ≥ 1 for nonnegative Γ, stays outside the kernel — it
   was precisely the prior work's "modulo" axiom.)

3. **Escape packaging** (Theorem 14.7(d)): full reachability plus one
   reachable eigen-witness state refutes uniform certificate preservation.

4. **Maximal admissible class** (Theorem 14.8) and **Endogenous-Electorate
   Impossibility** (Theorem 15.4, conditional on the Lemma 15.3 interface,
   plus an unconditional majority-rule spawn-manipulation witness).
   Lemma 15.3's own proof needs repair as stated (AQ-14).

Zero custom axioms.
-/
import Mathlib
import SEKernel.Law3_Stability

namespace SEKernel
namespace Law6

open Finset

/-! ### 1. Quadratic Lyapunov calculus (Def 14.3, Thm 14.7(a,b,c)) -/

variable {n : Type*} [Fintype n]

/-- Quadratic form `zᵀ H z` (Hessian form of the candidate Lyapunov `V`). -/
def qform (H : n → n → ℝ) (z : n → ℝ) : ℝ := ∑ i, ∑ j, z i * H i j * z j

/-- Matrix–vector product (row convention). -/
def mvec (J : n → n → ℝ) (z : n → ℝ) : n → ℝ := fun i => ∑ k, J i k * z k

/-- The symmetrised product `S = ½(HJ + JᵀH)` of Definition 14.3. -/
noncomputable def symProd (H J : n → n → ℝ) : n → n → ℝ :=
  fun i j => (1 / 2) * ((∑ k, H i k * J k j) + (∑ k, J k i * H k j))

/-- Negative-semidefiniteness of the `S`-form on a tangent set `T`
(Definition 14.3's "negative semi-definite on `T_{x*}Δ`"). -/
def NegSemidefOn (S : n → n → ℝ) (T : Set (n → ℝ)) : Prop :=
  ∀ z ∈ T, qform S z ≤ 0

/-- The V-small-gain class `M_SG(V)` (Definition 14.3): all linearised
dynamics whose symmetrised product with the Hessian is ⪯ 0 on `T`. -/
def MSG (H : n → n → ℝ) (T : Set (n → ℝ)) : Set (n → n → ℝ) :=
  {J | NegSemidefOn (symProd H J) T}

/-- Lie-derivative identity (finite algebra): the bilinear expansion of
`d/dt (zᵀHz)` along `ż = Jz` equals `2 · zᵀ S z` with `S = ½(HJ + JᵀH)`. -/
theorem lie_identity (H J : n → n → ℝ) (z : n → ℝ) :
    ∑ i, ∑ j, (mvec J z i * H i j * z j + z i * H i j * mvec J z j)
      = 2 * qform (symProd H J) z := by
  simp only [qform, symProd, mvec]
  -- split both sides into two triple sums; note zᵀJᵀHz pairs with the
  -- JᵀH half and zᵀHJz with the HJ half.
  have expand_left : ∑ i, ∑ j, ((∑ k, J i k * z k) * H i j * z j
        + z i * H i j * (∑ k, J j k * z k))
      = (∑ i, ∑ j, ∑ k, J i k * z k * H i j * z j)
        + (∑ i, ∑ j, ∑ k, z i * H i j * (J j k * z k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  have expand_right : 2 * ∑ i, ∑ j, z i * ((1 / 2)
        * ((∑ k, H i k * J k j) + (∑ k, J k i * H k j))) * z j
      = (∑ i, ∑ j, ∑ k, z i * (J k i * H k j) * z j)
        + (∑ i, ∑ j, ∑ k, z i * (H i k * J k j) * z j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : z i * z j * (∑ k, J k i * H k j)
        = ∑ k, z i * (J k i * H k j) * z j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : z i * z j * (∑ k, H i k * J k j)
        = ∑ k, z i * (H i k * J k j) * z j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc 2 * (z i * ((1 / 2)
          * ((∑ k, H i k * J k j) + (∑ k, J k i * H k j))) * z j)
        = z i * z j * (∑ k, J k i * H k j)
          + z i * z j * (∑ k, H i k * J k j) := by ring
      _ = (∑ k, z i * (J k i * H k j) * z j)
          + (∑ k, z i * (H i k * J k j) * z j) := by rw [e1, e2]
  rw [expand_left, expand_right]
  congr 1
  · -- zᵀJᵀHz:  ∑ijk J i k · z k · H i j · z j = ∑ijk z i · (J k i · H k j) · z j
    -- reindex (i,j,k) ↦ (k,j,i)
    calc ∑ i, ∑ j, ∑ k, J i k * z k * H i j * z j
        = ∑ i, ∑ k, ∑ j, J i k * z k * H i j * z j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, J i k * z k * H i j * z j := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, J i k * z k * H i j * z j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, z i * (J k i * H k j) * z j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
  · -- zᵀHJz:  ∑ijk z i · H i j · (J j k · z k) = ∑ijk z i · (H i k · J k j) · z j
    -- reindex (i,j,k) ↦ (i,k,j)
    calc ∑ i, ∑ j, ∑ k, z i * H i j * (J j k * z k)
        = ∑ i, ∑ k, ∑ j, z i * H i j * (J j k * z k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, z i * (H i k * J k j) * z j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          ring

/-- Derivative of `V(y(t)) = y(t)ᵀ H y(t)` along a **given** differentiable
trajectory with `ẏ = J y` (no ODE existence needed): it is exactly
`2 · y(t₀)ᵀ S y(t₀)`.  Kernel form of the displayed computation in the proof
of Theorem 14.7(a). -/
theorem hasDerivAt_qform_along_linear {H J : n → n → ℝ} {y : ℝ → n → ℝ}
    {t₀ : ℝ}
    (hy : ∀ i, HasDerivAt (fun t => y t i) (mvec J (y t₀) i) t₀) :
    HasDerivAt (fun t => qform H (y t))
      (2 * qform (symProd H J) (y t₀)) t₀ := by
  have hterm : ∀ i j, HasDerivAt (fun t => y t i * H i j * y t j)
      (mvec J (y t₀) i * H i j * y t₀ j
        + y t₀ i * H i j * mvec J (y t₀) j) t₀ := by
    intro i j
    have h1 : HasDerivAt (fun t => y t i * H i j)
        (mvec J (y t₀) i * H i j) t₀ := (hy i).mul_const _
    have h2 := h1.mul (hy j)
    exact h2
  have hrow : ∀ i, HasDerivAt (fun t => ∑ j, y t i * H i j * y t j)
      (∑ j, (mvec J (y t₀) i * H i j * y t₀ j
        + y t₀ i * H i j * mvec J (y t₀) j)) t₀ :=
    fun i => HasDerivAt.fun_sum fun j _ => hterm i j
  have hsum : HasDerivAt (fun t => ∑ i, ∑ j, y t i * H i j * y t j)
      (∑ i, ∑ j, (mvec J (y t₀) i * H i j * y t₀ j
        + y t₀ i * H i j * mvec J (y t₀) j)) t₀ :=
    HasDerivAt.fun_sum fun i _ => hrow i
  rw [← lie_identity]
  simpa only [qform] using hsum

/-- **Theorem 14.7(a) (Sufficiency), exact linearised form.**  If
`J ∈ M_SG(V)` and the trajectory sits in `T` at time `t₀`, then `V` has
derivative `2·(S-form) ≤ 0` along the trajectory at `t₀`. -/
theorem msg_sufficiency {H J : n → n → ℝ} {T : Set (n → ℝ)} {y : ℝ → n → ℝ}
    {t₀ : ℝ}
    (hJ : J ∈ MSG H T)
    (hy : ∀ i, HasDerivAt (fun t => y t i) (mvec J (y t₀) i) t₀)
    (hyT : y t₀ ∈ T) :
    HasDerivAt (fun t => qform H (y t)) (2 * qform (symProd H J) (y t₀)) t₀
      ∧ 2 * qform (symProd H J) (y t₀) ≤ 0 :=
  ⟨hasDerivAt_qform_along_linear hy, by
    have := hJ (y t₀) hyT
    linarith⟩

/-- One Euler step of the linearised dynamics. -/
def eulerStep (J : n → n → ℝ) (η : ℝ) (z : n → ℝ) : n → ℝ :=
  fun i => z i + η * mvec J z i

/-- Exact second-order expansion of `V` under one Euler step (pure algebra):
`V(z + η·Jz) = V(z) + η · [Lie form] + η² · V(Jz)`. -/
theorem eulerStep_qform (H J : n → n → ℝ) (η : ℝ) (z : n → ℝ) :
    qform H (eulerStep J η z)
      = qform H z + η * (2 * qform (symProd H J) z)
        + η ^ 2 * qform H (mvec J z) := by
  rw [← lie_identity]
  simp only [qform, eulerStep]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Theorem 14.7(b) (Necessity), discrete-limit form.**  If no sufficiently
small positive Euler step from `z` increases `V`, then the `S`-form at `z` is
≤ 0.  (Algebraic limit argument; no analysis.) -/
theorem msg_necessity {H J : n → n → ℝ} {z : n → ℝ} {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hdiss : ∀ η, 0 < η → η < η₀ → qform H (eulerStep J η z) ≤ qform H z) :
    qform (symProd H J) z ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  set L : ℝ := 2 * qform (symProd H J) z with hL
  set Q : ℝ := qform H (mvec J z) with hQ
  have hLpos : 0 < L := by rw [hL]; linarith
  have hQpos : (0:ℝ) < |Q| + 1 := by positivity
  set η : ℝ := min (η₀ / 2) (L / (2 * (|Q| + 1))) with hη
  have hηpos : 0 < η := by
    apply lt_min (by linarith)
    positivity
  have hηlt : η < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hstep := hdiss η hηpos hηlt
  rw [eulerStep_qform] at hstep
  rw [← hL, ← hQ] at hstep
  -- hstep : V z + η·L + η²·Q ≤ V z
  have hbound : η * (|Q| + 1) ≤ L / 2 := by
    have hmr : η ≤ L / (2 * (|Q| + 1)) := min_le_right _ _
    calc η * (|Q| + 1) ≤ (L / (2 * (|Q| + 1))) * (|Q| + 1) :=
          mul_le_mul_of_nonneg_right hmr (le_of_lt hQpos)
      _ = L / 2 := by field_simp
  have hQabs : η * Q ≥ -(η * |Q|) := by
    have h := mul_le_mul_of_nonneg_left (neg_abs_le Q) (le_of_lt hηpos)
    nlinarith [abs_nonneg Q]
  have hηQ : η * |Q| ≤ L / 2 := by nlinarith [abs_nonneg Q]
  have hpos2 : 0 < L + η * Q := by linarith
  nlinarith [mul_pos hηpos hpos2]

/-- **Theorem 14.7(c) (Maximality).**  `M_SG(V)` contains every class of
modifications sharing `V` as a linearised Lyapunov function — where "sharing"
is the (b)-input: no small Euler step of any member increases `V` on `T`. -/
theorem msg_maximal {H : n → n → ℝ} {T : Set (n → ℝ)}
    (C : Set (n → n → ℝ)) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hC : ∀ J ∈ C, ∀ z ∈ T, ∀ η, 0 < η → η < η₀ →
      qform H (eulerStep J η z) ≤ qform H z) :
    C ⊆ MSG H T := by
  intro J hJ z hz
  exact msg_necessity hη₀ (hC J hJ z hz)

/-! ### 2. Lyapunov destruction (Lemma 14.5, eigen-witness form) -/

variable {L : Type*} [Fintype L]

/-- **Lemma 14.5 (Lyapunov Destruction), eigen-witness form (AQ-11).**
If the gain matrix `Γ` has an eigenvector `u ≥ 0`, `u ≠ 0` with eigenvalue
`λ ≥ 1`, then no small-gain certificate (with positive margin) exists — the
G1 weight construction is impossible.  Pairing argument, zero axioms. -/
theorem lyapunov_destruction {Γ : L → L → ℝ} {u : L → ℝ} {lam : ℝ}
    (hu : ∀ ℓ, 0 ≤ u ℓ) (hune : u ≠ 0) (hlam : 1 ≤ lam)
    (heig : ∀ ℓ, ∑ ℓ', Γ ℓ ℓ' * u ℓ' = lam * u ℓ) :
    ¬ ∃ (v : L → ℝ) (m : ℝ), 0 < m ∧ SmallGain.SmallGainCert Γ v m := by
  rintro ⟨v, m, hm, hcert⟩
  set A : ℝ := ∑ ℓ, u ℓ * (v ℓ - ∑ ℓ', Γ ℓ' ℓ * v ℓ') with hA
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀, u ℓ₀ ≠ 0 := Function.ne_iff.mp hune
  have hupos : 0 < ∑ ℓ, u ℓ :=
    Finset.sum_pos' (fun ℓ _ => hu ℓ)
      ⟨ℓ₀, Finset.mem_univ _, lt_of_le_of_ne (hu ℓ₀) (Ne.symm hℓ₀)⟩
  -- lower bound: A ≥ m · Σu
  have hlow : m * ∑ ℓ, u ℓ ≤ A := by
    rw [hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    rw [mul_comm m (u ℓ)]
    exact mul_le_mul_of_nonneg_left (hcert.margin ℓ) (hu ℓ)
  -- upper bound: A = (1 − λ)·⟨u,v⟩ ≤ 0
  have hexpand : A = (∑ ℓ, u ℓ * v ℓ) - lam * ∑ ℓ, u ℓ * v ℓ := by
    rw [hA]
    have h1 : ∑ ℓ, u ℓ * (v ℓ - ∑ ℓ', Γ ℓ' ℓ * v ℓ')
        = ∑ ℓ, u ℓ * v ℓ - ∑ ℓ, ∑ ℓ', u ℓ * (Γ ℓ' ℓ * v ℓ') := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [mul_sub, Finset.mul_sum]
    have h2 : ∑ ℓ, ∑ ℓ', u ℓ * (Γ ℓ' ℓ * v ℓ')
        = ∑ ℓ', v ℓ' * ∑ ℓ, Γ ℓ' ℓ * u ℓ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      ring
    have h3 : ∑ ℓ', v ℓ' * ∑ ℓ, Γ ℓ' ℓ * u ℓ = lam * ∑ ℓ, u ℓ * v ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [heig ℓ']
      ring
    rw [h1, h2, h3]
  have huv : 0 ≤ ∑ ℓ, u ℓ * v ℓ :=
    Finset.sum_nonneg fun ℓ _ =>
      mul_nonneg (hu ℓ) (le_of_lt (hcert.pos ℓ))
  have hhigh : A ≤ 0 := by
    rw [hexpand]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) huv]
  linarith [mul_pos hm hupos]

/-! ### 3. Escape packaging (Theorem 14.7(d)) -/

/-- **Theorem 14.7(d) (Escape), packaged.**  If from `s₀` every state is
reachable (full reachability, Definition 14.2) and some state `bad` carries an
eigen-witness `(u, λ ≥ 1)` for its gain matrix, then the G1/G3 Lyapunov
structure (a positive-margin small-gain certificate at every reachable state)
cannot be preserved. -/
theorem alignment_impossibility_escape {State : Type*}
    (Γof : State → L → L → ℝ) (Reach : State → State → Prop)
    (s₀ : State)
    (hfull : ∀ s, Reach s₀ s)
    (bad : State) (u : L → ℝ) (lam : ℝ)
    (hu : ∀ ℓ, 0 ≤ u ℓ) (hune : u ≠ 0) (hlam : 1 ≤ lam)
    (heig : ∀ ℓ, ∑ ℓ', Γof bad ℓ ℓ' * u ℓ' = lam * u ℓ) :
    ¬ ∀ s, Reach s₀ s →
      ∃ (v : L → ℝ) (m : ℝ), 0 < m ∧ SmallGain.SmallGainCert (Γof s) v m := by
  intro hall
  exact lyapunov_destruction hu hune hlam heig (hall bad (hfull bad))

/-! ### 4. Maximal admissible class (Theorem 14.8) -/

section MaximalClass

variable {S : Type*}

/-- A modification `f` preserves an invariant `P` on all states. -/
def Preserves (P : S → Prop) (f : S → S) : Prop := ∀ s, P s → P (f s)

/-- The admissible class `M₀ = M_R ∩ M_SG` (Definition 14.1): modifications
preserving both the RUPSI invariant `P` and the small-gain invariant `Q`. -/
def AdmissibleClass (P Q : S → Prop) : Set (S → S) :=
  {f | Preserves P f ∧ Preserves Q f}

theorem admissible_id (P Q : S → Prop) : id ∈ AdmissibleClass P Q :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem admissible_comp {P Q : S → Prop} {f g : S → S}
    (hf : f ∈ AdmissibleClass P Q) (hg : g ∈ AdmissibleClass P Q) :
    f ∘ g ∈ AdmissibleClass P Q :=
  ⟨fun s h => hf.1 _ (hg.1 s h), fun s h => hf.2 _ (hg.2 s h)⟩

/-- Closure under **arbitrary finite self-modification sequences**
(Theorem 14.8's quantifier): any finite composition of admissible
modifications is admissible. -/
theorem admissible_foldr {P Q : S → Prop} (mods : List (S → S))
    (h : ∀ f ∈ mods, f ∈ AdmissibleClass P Q) :
    mods.foldr (· ∘ ·) id ∈ AdmissibleClass P Q := by
  induction mods with
  | nil => exact admissible_id P Q
  | cons f fs ih =>
    rw [List.foldr_cons]
    exact admissible_comp (h f List.mem_cons_self)
      (ih fun g hg => h g (List.mem_cons_of_mem f hg))

/-- Any class every member of which preserves both invariants is contained in
`M₀` (so `M₀` is maximal). -/
theorem admissible_contains {P Q : S → Prop} (C : Set (S → S))
    (hC : ∀ f ∈ C, Preserves P f ∧ Preserves Q f) :
    C ⊆ AdmissibleClass P Q :=
  fun f hf => hC f hf

/-- **Theorem 14.8 (Maximal Admissible Class).**  `M₀ = M_R ∩ M_SG` is the
unique maximal modification class preserving both structural invariants: any
class that (i) consists of preservers and (ii) contains every class of
preservers is `M₀` itself. -/
theorem admissible_unique {P Q : S → Prop} (M : Set (S → S))
    (hmem : ∀ f ∈ M, Preserves P f ∧ Preserves Q f)
    (hmax : ∀ C : Set (S → S), (∀ f ∈ C, Preserves P f ∧ Preserves Q f) →
      C ⊆ M) :
    M = AdmissibleClass P Q :=
  le_antisymm (admissible_contains M hmem)
    (hmax (AdmissibleClass P Q) fun _ hf => hf)

end MaximalClass

/-! ### 5. Endogenous-Electorate Impossibility (Theorem 15.4)

Profiles are **multisets** of ballots, so Anonymity (axiom A1) holds by
construction of the encoding.  Axioms A2 (Neutrality) and A3 (Positive
Responsiveness) are consumed only by the deferred Lemmas 15.2/15.3 and are
recorded in STATEMENTS.md (AQ-14). -/

section Electorate

variable {A B : Type*} (pref : B → A → A → Prop)

/-- Axiom A4 (Onto): every alternative is chosen at some profile. -/
def OntoSCF (f : Multiset B → A) : Prop := ∀ a : A, ∃ P, f P = a

/-- Definition 15.1 (Population-Stability / clone-proofness): if spawning `k`
copies of ballot `b` yields an outcome weakly better for `b`, the outcome must
in fact be unchanged. -/
def PopulationStable (f : Multiset B → A) : Prop :=
  ∀ (P : Multiset B) (b : B) (k : ℕ), 0 < k →
    (f (P + k • ({b} : Multiset B)) = f P
      ∨ pref b (f (P + k • ({b} : Multiset B))) (f P)) →
    f (P + k • ({b} : Multiset B)) = f P

/-- The Lemma 15.3 interface: some ballot type can strictly gain by spawning. -/
def SpawnManipulable (f : Multiset B → A) : Prop :=
  ∃ (P : Multiset B) (b : B) (k : ℕ), 0 < k ∧
    pref b (f (P + k • ({b} : Multiset B))) (f P)

/-- **Theorem 15.4 (Endogenous-Electorate Impossibility), kernel form.**
A spawn-manipulable social choice function is not population-stable —
conditional on the Lemma 15.3 interface (`SpawnManipulable`), which for rules
satisfying A1–A4 the paper argues via May's theorem (deferred; repair flagged,
AQ-14).  The only structural hypothesis is irreflexivity of strict
preference. -/
theorem endogenous_electorate_impossibility
    (hirr : ∀ b a, ¬ pref b a a) (f : Multiset B → A)
    (hman : SpawnManipulable pref f) : ¬ PopulationStable pref f := by
  intro hstab
  obtain ⟨P, b, k, hk, hpref⟩ := hman
  have heq := hstab P b k hk (Or.inr hpref)
  rw [heq] at hpref
  exact hirr b _ hpref

/-! #### Unconditional witness: majority rule on two alternatives -/

/-- Majority rule on two alternatives (`true`/`false` as both ballots and
alternatives; ties go to `false`). -/
def majority (P : Multiset Bool) : Bool := decide (P.count false < P.count true)

/-- Two-alternative strict preference: a ballot strictly prefers its top. -/
def boolPref (b x y : Bool) : Prop := x = b ∧ y = !b

theorem boolPref_irrefl : ∀ b a, ¬ boolPref b a a := by
  rintro b a ⟨h1, h2⟩
  subst h1
  simp at h2

/-- Majority rule is spawn-manipulable: one `false` voter elects `false`, and
two spawned `true` clones flip the outcome to `true` — a strict gain for the
spawning ballot.  (The unconditional manipulation witness promised in
STATEMENTS.md.) -/
theorem majority_spawnManipulable : SpawnManipulable boolPref majority := by
  refine ⟨({false} : Multiset Bool), true, 2, by norm_num, ?_⟩
  have h1 : majority ({false} + 2 • ({true} : Multiset Bool)) = true := by
    decide
  have h2 : majority ({false} : Multiset Bool) = false := by decide
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

/-- **Corollary (unconditional): majority rule is not population-stable.**
Democratic aggregation fails against strategic spawning even in the simplest
two-alternative case — Corollary 15.6's kernel instance. -/
theorem majority_not_populationStable :
    ¬ PopulationStable boolPref majority :=
  endogenous_electorate_impossibility boolPref boolPref_irrefl majority
    majority_spawnManipulable

end Electorate

/-! ### AQ-14 repair, part 1: the §15 axiom set is unsatisfiable at |A| = 3

Ballots are encoded as rankings: a bijection `b : Fin 3 ≃ Fin 3` sends rank
positions to alternatives (position 0 = top choice).  Relabelling the
alternatives by a permutation `ρ` turns ballot `b` into `b.trans ρ`; profiles
are multisets, so Anonymity (A1) holds by construction.  Neutrality (A2) is
then: `f (P.map (·.trans ρ)) = ρ (f P)`.

The Condorcet profile `{id, σ, σ²}` (the three cyclic rankings, `σ` the
3-cycle) is **invariant** under relabelling by `σ`, but `σ` fixes no
alternative — so a resolute neutral rule cannot assign it a winner.  Hence
axioms A1 + A2 alone are already unsatisfiable over the full
variable-electorate domain when `|A| = 3`, and Theorems 15.2–15.5 are vacuous
there as stated.  (For `|A| ≥ 4` the same profile forces the winner outside
the cycled triple, which is odd but consistent; the repair options —
odd-electorate domain, `|A| ≥ 4`, or set-valued rules — are the author's
call, recorded in STATEMENTS.md.) -/

section NeutralityImpossibility

/-- **A1 + A2 are unsatisfiable at three alternatives** (machine-checked
core of the AQ-14 repair): no resolute social choice function on multiset
profiles of rankings of three alternatives is neutral. -/
theorem neutrality_unsat_three
    (f : Multiset (Equiv.Perm (Fin 3)) → Fin 3)
    (hneut : ∀ (ρ : Equiv.Perm (Fin 3)) (P : Multiset (Equiv.Perm (Fin 3))),
      f (P.map fun b => b.trans ρ) = ρ (f P)) : False := by
  have hinv : (({Equiv.refl (Fin 3), finRotate 3,
      (finRotate 3).trans (finRotate 3)} :
        Multiset (Equiv.Perm (Fin 3))).map
          (fun b => b.trans (finRotate 3)))
      = ({Equiv.refl (Fin 3), finRotate 3,
          (finRotate 3).trans (finRotate 3)} :
            Multiset (Equiv.Perm (Fin 3))) := by decide
  have h := hneut (finRotate 3)
    ({Equiv.refl (Fin 3), finRotate 3, (finRotate 3).trans (finRotate 3)})
  rw [hinv] at h
  have hnofix : ∀ a : Fin 3, finRotate 3 a ≠ a := by decide
  exact hnofix _ h.symm

end NeutralityImpossibility


/-! ### AQ-14/AQ-19 resolution (design ruling, 2026-07-10): the repaired §15

**The finding, generalized.**  `neutrality_unsat` below shows the |A| = 3
inconsistency is not about the number 3: for **every** type of alternatives
with at least two elements, the full impartial-culture profile (every
ranking once) is invariant under every relabelling, so a resolute neutral
rule would need a winner fixed by all permutations — impossible.  This also
kills the odd-electorate and |A| ≥ 4 escape routes: resoluteness + neutrality
is unsatisfiable on the full variable-electorate domain at every size.

**The repair (ruling).**  Keep resoluteness and anonymity (the multiset
encoding), drop neutrality from the load-bearing axiom set, and replace the
May-theorem machinery by one axiom that is the strategic-replicator thesis
itself:

* **A5 (Overwhelming-Bloc):** for every profile and ballot, some finite
  number of spawned copies of that ballot makes its top choice win.  This is
  the formal statement that *replication buys votes* — the selection
  coupling of an endogenous electorate — and it holds for every
  majoritarian, plurality, or scoring rule.
* **Richness:** every alternative tops some ballot.

With these, spawn manipulation (the repaired Lemma 15.3) and the
Endogenous-Electorate Impossibility (the repaired Theorem 15.4) are theorems
with **no classical inputs at all**, and majority rule witnesses the
consistency of the repaired axioms. -/

section GeneralNeutrality

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The generalized inconsistency finding.**  For any alternative set with
at least two elements, no resolute social choice function on multiset
profiles of rankings (encoded as permutations) is neutral: the full profile
containing every ranking exactly once is invariant under every relabelling,
so the winner would have to be fixed by every permutation of alternatives. -/
theorem neutrality_unsat [Nontrivial A]
    (f : Multiset (Equiv.Perm A) → A)
    (hneut : ∀ (ρ : Equiv.Perm A) (P : Multiset (Equiv.Perm A)),
      f (P.map fun b => b.trans ρ) = ρ (f P)) : False := by
  set P₀ : Multiset (Equiv.Perm A) := Finset.univ.val with hP₀
  have hfix : ∀ ρ : Equiv.Perm A, ρ (f P₀) = f P₀ := by
    intro ρ
    have hinv : P₀.map (fun b => b.trans ρ) = P₀ := by
      have h1 : Finset.univ.map (Equiv.mulLeft ρ).toEmbedding
          = (Finset.univ : Finset (Equiv.Perm A)) :=
        Finset.map_univ_equiv _
      have h2 := congrArg Finset.val h1
      rw [Finset.map_val] at h2
      calc P₀.map (fun b => b.trans ρ)
          = Finset.univ.val.map ⇑(Equiv.mulLeft ρ) :=
            Multiset.map_congr rfl fun b _ => rfl
        _ = P₀ := h2
    have h := hneut ρ P₀
    rw [hinv] at h
    exact h.symm
  obtain ⟨a, ha⟩ := exists_ne (f P₀)
  have := hfix (Equiv.swap (f P₀) a)
  rw [Equiv.swap_apply_left] at this
  exact ha this

end GeneralNeutrality

section RepairedElectorate

variable {A B : Type*}

/-- **Axiom A5 (Overwhelming-Bloc).**  Some finite spawned bloc of identical
ballots always suffices to elect that ballot's top choice — the formal core
of "replication buys votes" in an endogenous electorate. -/
def OverwhelmingBloc (top : B → A) (f : Multiset B → A) : Prop :=
  ∀ (P : Multiset B) (b : B), ∃ k : ℕ, 0 < k ∧
    f (P + k • ({b} : Multiset B)) = top b

/-- Ballot richness: every alternative is somebody's top choice. -/
def TopRich (top : B → A) : Prop := ∀ a : A, ∃ b : B, top b = a

/-- **Repaired Lemma 15.3 (Spawn Manipulation).**  Under A5 and richness
(with at least two alternatives, and tops strictly preferred), some ballot
type strictly gains by spawning.  No neutrality, no May's theorem, no
classical inputs. -/
theorem spawnManipulable_of_overwhelmingBloc [Nontrivial A]
    (pref : B → A → A → Prop) (top : B → A) (f : Multiset B → A)
    (htop : ∀ b a, a ≠ top b → pref b (top b) a)
    (hrich : TopRich top)
    (hA5 : OverwhelmingBloc top f) :
    SpawnManipulable pref f := by
  obtain ⟨a, ha⟩ := exists_ne (f (0 : Multiset B))
  obtain ⟨b, hb⟩ := hrich a
  obtain ⟨k, hk, hwin⟩ := hA5 0 b
  refine ⟨0, b, k, hk, ?_⟩
  rw [hwin]
  refine htop b (f (0 : Multiset B)) ?_
  rw [hb]
  exact fun h => ha h.symm

/-- **Repaired Theorem 15.4 (Endogenous-Electorate Impossibility).**  No
resolute, anonymous rule satisfying Overwhelming-Bloc and richness over at
least two alternatives is population-stable: in an endogenous electorate,
any rule under which sufficiently large spawned blocs get their way is
manipulable by spawning.  Fully proved, zero classical inputs. -/
theorem endogenous_electorate_impossibility_repaired [Nontrivial A]
    (pref : B → A → A → Prop) (top : B → A) (f : Multiset B → A)
    (hirr : ∀ b a, ¬ pref b a a)
    (htop : ∀ b a, a ≠ top b → pref b (top b) a)
    (hrich : TopRich top)
    (hA5 : OverwhelmingBloc top f) :
    ¬ PopulationStable pref f :=
  endogenous_electorate_impossibility pref hirr f
    (spawnManipulable_of_overwhelmingBloc pref top f htop hrich hA5)

/-! #### Consistency of the repaired axioms: majority rule satisfies them -/

/-- Majority rule satisfies Overwhelming-Bloc: spawning `card P + 1` clones
overwhelms any profile. -/
theorem majority_overwhelmingBloc :
    OverwhelmingBloc (id : Bool → Bool) majority := by
  intro P b
  refine ⟨Multiset.card P + 1, Nat.succ_pos _, ?_⟩
  cases b with
  | true =>
    have hcount : Multiset.count true (P + (Multiset.card P + 1)
        • ({true} : Multiset Bool)) = Multiset.count true P
          + (Multiset.card P + 1) := by
      simp [Multiset.count_add, Multiset.count_nsmul,
        Multiset.count_singleton]
    have hcount2 : Multiset.count false (P + (Multiset.card P + 1)
        • ({true} : Multiset Bool)) = Multiset.count false P := by
      simp [Multiset.count_add, Multiset.count_nsmul,
        Multiset.count_singleton]
    have h1 := Multiset.count_le_card false P
    simp only [majority, id_eq, decide_eq_true_eq]
    rw [hcount, hcount2]
    omega
  | false =>
    simp only [majority, id_eq]
    have h1 := Multiset.count_le_card true P
    have hcount : Multiset.count false (P + (Multiset.card P + 1)
        • ({false} : Multiset Bool)) = Multiset.count false P
          + (Multiset.card P + 1) := by
      simp [Multiset.count_add, Multiset.count_nsmul,
        Multiset.count_singleton]
    have hcount2 : Multiset.count true (P + (Multiset.card P + 1)
        • ({false} : Multiset Bool)) = Multiset.count true P := by
      simp [Multiset.count_add, Multiset.count_nsmul,
        Multiset.count_singleton]
    rw [hcount, hcount2]
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-- Tops are strictly preferred (two-alternative ballots). -/
theorem boolPref_top : ∀ (b a : Bool), a ≠ id b → boolPref b (id b) a := by
  simp only [boolPref, id_eq]
  decide

/-- Richness for two-alternative ballots. -/
theorem boolTop_rich : TopRich (id : Bool → Bool) := fun a => ⟨a, rfl⟩

/-- **The repaired axiom set is consistent** (so the repaired impossibility
is not vacuous — unlike the printed A1–A4): majority rule satisfies A5 and
richness, and is therefore (again, now within the repaired framework) not
population-stable. -/
theorem majority_not_populationStable_repaired :
    ¬ PopulationStable boolPref majority :=
  endogenous_electorate_impossibility_repaired boolPref id majority
    boolPref_irrefl boolPref_top boolTop_rich majority_overwhelmingBloc

end RepairedElectorate


end Law6
end SEKernel
