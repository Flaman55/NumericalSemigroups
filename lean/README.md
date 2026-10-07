# LinearQ — Lean 4 Formalization

Lean 4 / Mathlib formalization of the core definitions and main theorems from:

> **A Linear Algorithm for Huang's Quadratic Form on Numerical Semigroups and Density Asymptotics**
> Artur Flamandzki, 2026
> https://zenodo.org/records/20261427

## Structure

| File | Contents |
|------|----------|
| `LinearQ/Block1_KIntervals.lean` | Kernel `K(d)` — definition and piecewise interval structure |
| `LinearQ/Block2_QReduction.lean` | Quadratic form `Q` and sliding-window reduction (Theorem 1.1) |
| `LinearQ/Block3_MultiGenerator.lean` | Generalised kernel `K^(n)` — recursive definition and support bound `w(n) ≤ σ(n)` |
| `LinearQ/Block4_DensityAsymptotic.lean` | Density asymptotic theorem: `w(n)/(2^n−1) = o(P(n))` (Theorem 1.5) |

## Main theorems

- **`quadForm_eq_linearForm`** (Block 2): `Q(n) = Σ_k n_k (W⁺_k − W⁻_k)` — the linear-time reduction for two generators.
- **`w_le_sigma`** (Block 3): `w(ps) ≤ σ(ps)` — active window count bounded by generator sum.
- **`gap_div_mertens_tendsto_one`** (Block 4): `(P(n) − w(n)/(2^n−1)) / P(n) → 1`.
- **`windowCount_isLittleO_mertensProd`** (Block 4): `w(n)/(2^n−1) = o(P(n))` in Landau notation.

## Build

Requires Lean 4 and Mathlib (toolchain: `leanprover/lean4:v4.35.0-rc2`).

```bash
cd lean
lake update
lake build
```

## Note on self-verification

This formalization was developed by the paper's author. The build passes, but independent
re-verification would be the true gold standard. The formalization is shared here as a
reference and starting point for external review.
