# TSE Formal: Lean 4 Formalization of the Theory of Strategic Evolution

Formal verification of the Seven Laws of Strategic Replicators in Lean 4 with Mathlib4.

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-green.svg)](https://github.com/leanprover-community/mathlib4)
[![Paper](https://img.shields.io/badge/Paper-arXiv-red.svg)](https://arxiv.org/abs/XXXX.XXXXX)

---

## Overview

This repository contains formal proofs for the Theory of Strategic Evolution (TSE), which analyzes strategic replicators: AI systems that optimize utility functions and control their own replication.

The formalization covers:
- RUPSI axiom system
- Games with Endogenous Players (GEPs)
- Replicator dynamics and Lyapunov stability
- ESDI characterization (existence, sparsity, equivalence)
- Small-gain condition for multi-level systems
- G∞ closure theorem
- Alignment impossibility
- Hopf bifurcation at stability threshold

---

## The Seven Laws

| Law | Status | Main File |
|-----|--------|-----------|
| Law 1: Strategic Selection | ✓ Verified | `Basin.lean` |
| Law 2: ESDI Characterization | ✓ Fully machine-checked | `ESDI.lean` |
| Law 3: H-γ Stability | ✓ Fully machine-checked | `SmallGain.lean` |
| Law 4: G∞ Closure | ✓ Verified (modulo spectral) | `GInfinityExtension.lean` |
| Law 5: Constitutional Duality | ✓ Verified | `WelfareTheorems.lean` |
| Law 6: Alignment Impossibility | ✓ Verified | `AlignmentImpossibility.lean` |
| Law 7: Hopf Transition | ✓ Verified (modulo bifurcation) | `HopfBifurcation.lean` |

---

## Repository Structure

### Core Definitions
- `Basic.lean` — Fundamental types and structures
- `CRUPSI.lean` — RUPSI axiom formalization
- `ESDI.lean` — Evolutionarily Stable Distributions of Intelligence

### Stability Theory
- `Basin.lean` — Stability basins and Lyapunov functions
- `SmallGain.lean` — Small-gain condition and spectral radius
- `HopfBifurcation.lean` — Bifurcation at γ = 1

### Alignment and Modification
- `AlignmentImpossibility.lean` — Law 6 main theorem
- `AlignmentImpossibilityProofs.lean` — Supporting lemmas
- `GInfinityExtension.lean` — G∞ closure theorem
- `GInfinityModifications.lean` — Modification class structure

### Game Theory
- `Frontier.lean` — ROC frontier geometry
- `Cooperation.lean` — Cooperation thresholds
- `Democracy.lean` — Endogenous-electorate impossibility

### Extensions
- `G10Validity.lean` — Evolvability bounds
- `G11Evolvability.lean` — Innovation dynamics
- `G12ConstitutionalSelection.lean` — Constitutional meta-governance
- `WelfareTheorems.lean` — Welfare theorem extensions
- `HeterogeneousWelfare.lean` — Heterogeneous fitness

### Supporting Mathematics
- `PerronFrobenius.lean` — Spectral theory for non-negative matrices
- `NeumannSeries.lean` — Series convergence for stability
- `HelmholtzDecomposition.lean` — Potential game structure
- `Sparsity.lean` — Constraint-driven sparsity

---

## Key Theorems

### ESDI Existence and Sparsity
```lean
theorem esdi_exists (sys : RUPSISystem) : ∃ x : ESDI sys, True

theorem esdi_sparsity (x : ESDI sys) (h : binding_constraints sys x = m) :
  (support x).card ≤ m
```

### Small-Gain Stability
```lean
theorem small_gain_stability (Γ : Matrix n n ℝ) (hΓ : spectral_radius Γ < 1) :
  ∃ V : Lyapunov, joint_lyapunov V
```

### Alignment Impossibility
```lean
theorem alignment_impossible (sys : ModifiableSystem) 
  (h : full_reachability sys) :
  ∀ B : StabilityBasin, ∃ path : ModificationSequence, escapes path B
```

### G∞ Closure
```lean
theorem admissible_closed (φ ψ : Modification) 
  (hφ : φ ∈ M₀) (hψ : ψ ∈ M₀) : 
  (ψ ∘ φ) ∈ M₀
```

---

## Building

Requires Lean 4 and Mathlib4.

```bash
lake build
```

---

## Axioms Used

Some proofs rely on standard mathematical axioms not yet in Mathlib:
- Spectral theory for general matrices
- ODE existence and uniqueness (Picard-Lindelöf)
- Hopf bifurcation theorem

These are marked with `sorry` or `axiom` declarations.

---

## Connection to Paper

This formalization accompanies:

> Vallier, Kevin. "The Theory of Strategic Evolution: Games with Endogenous Players and the Seven Laws of Strategic Replicators." arXiv:XXXX.XXXXX (2025).

Each `.lean` file corresponds to sections in the paper. Comments reference theorem numbers.

---

## Key Concepts Formalized

### Strategic Replicator
```lean
structure StrategicReplicator where
  utility : UtilityFunction
  budget : ResourceBudget  
  spawn : SpawnDecision
  selection : SelectionPressure
```

### RUPSI System
```lean
structure RUPSISystem where
  rival : RivalResources
  utility_guided : UtilityGuided
  performance_mapped : PerformanceMapped
  selection_monotone : SelectionMonotone
  innovation_rare : InnovationRare
```

### Modification Class
```lean
def ModificationClass := Set Modification

def admissible (M : ModificationClass) : Prop :=
  preserves_replicator_structure M ∧ preserves_small_gain M
```

---

## Contributing

Issues and PRs welcome. Priority areas:
- Completing spectral theory axioms
- Formalizing ODE existence
- Extending to continuous strategy spaces

---

## Citation

```bibtex
@software{vallier2025tseformal,
  title={TSE Formal: Lean 4 Formalization of the Theory of Strategic Evolution},
  author={Vallier, Kevin},
  year={2025},
  url={https://github.com/kevinvallier/TSE_Formal}
}
```

---

## License

MIT License

---

## Keywords

Lean 4, Mathlib4, formal verification, theorem proving, game theory, evolutionary dynamics, AI alignment, replicator dynamics, Lyapunov stability, spectral theory, impossibility theorems
