# NumericalSemigroups

Lean 4 / Mathlib formalization, numerical verification scripts and paper for:

> **A Linear Algorithm for Huang's Quadratic Form on Numerical Semigroups and Density Asymptotics**
> Artur Flamandzki, 2026
> https://zenodo.org/records/20261427

The quadratic form studied here is due to Yifeng Huang (arXiv:2604.13238). License: Apache-2.0.

## Lean formalization

Requires the toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`.

```bash
lake exe cache get
lake build
```

### What is formalized

For generators `p_1,...,p_n` the kernel `K^(n)(d)` is the inclusion-exclusion sum over
sub-multisets `S` of `(-1)^|S| * 1[d >= sigma(S)]`. It is a step function whose jumps are
`pi(s) = K(s) - K(s-1)`. An *active window* is an interval between consecutive breakpoints
on which `K^(n)` is nonzero; the Lean development counts windows by their left endpoints.

| Result | Lean declaration |
|---|---|
| Theorem 1.1 (two generators): `Q(n) = sum_k n_k (W+_k - W-_k)` | `LinearQ.quadForm_eq_linearForm` (Block 2) |
| Recursive kernel equals the inclusion-exclusion kernel | `LinearQ.kernelK_multi_eq_inclExcl` (Block 3b) |
| Theorem 1.2: `Q(n) = sum over breakpoints of pi(s) * T(s)`, at most `sigma + 1` breakpoints | `LinearQ.quadFormMulti_eq_breakpoint_sum`, `LinearQ.breakpointSet_card_le` (Block 5) |
| Theorem 1.2: `w <= sigma` (pigeonhole) | `LinearQ.activeWindowCount_le_sigma` (Block 3b) |
| Theorem 1.5: `w(n)/(2^n - 1) = o(P(n))`, equivalently `delta(n)/P(n) -> 1` | `LinearQ.windowCount_isLittleO_mertensProd`, `LinearQ.gap_div_mertens_tendsto_one` (Block 4) |

The running-time claims of the paper (O(N), O(n sigma_n)), its numerical tables and its
conjectures are not formalized. See `formalization.yaml` (`fidelity`) for the exact list of
differences between the paper and the Lean statements, for example that Theorem 1.5 is stated
for strictly increasing generators.

### Layout

| Path | Contents |
|---|---|
| `LinearQ/Block1_KIntervals.lean` | Two-generator kernel and its piecewise interval structure |
| `LinearQ/Block2_QReduction.lean` | Quadratic form and sliding-window reduction (Theorem 1.1) |
| `LinearQ/Block3_MultiGenerator.lean` | Recursive multi-generator kernel and support bounds |
| `LinearQ/Block3_Windows.lean` | Inclusion-exclusion form, jumps, active windows, `w <= sigma` |
| `LinearQ/Block4_DensityAsymptotic.lean` | Density asymptotics (Theorem 1.5) |
| `LinearQ/Block5_Breakpoints.lean` | Breakpoint decomposition of the multi-generator quadratic form |
| `Challenge.lean`, `Solution.lean`, `comparator.json` | Statement file, proofs and comparator configuration |

### Production and review

The original Lean files (Block 1 to Block 4) and the paper text were written by an AI agent
(Claude Code) under the author's direction; Block 3b, Block 5, the port to Lean's module
system, `Challenge.lean` and `Solution.lean` were written by an AI agent (Claude, in Claude
Cowork) in an October 2026 session, with every build run by the author. The mathematics is the
author's; Lean's kernel decides correctness. The author has not read the Lean source line by
line, and independent verification would be valuable. Details are in `formalization.yaml`.

## Numerical verification scripts (Python)

## Files

| File | Purpose | Appendix table |
|---|---|---|
| `core.py` | Shared building blocks: gap sets, kernels K and K⁽ⁿ⁾, active windows | — |
| `verify_linear_Q.py` | Three-way comparison O(N²) vs O(N log N) vs O(N) for Theorems 1.1–1.2 | A.2, A.3 |
| `incremental_windows.py` | `IncrementalWindowBuilder` class + verification vs naive O(2ⁿ) | — |
| `appendix_verify.py` | Density data (n ≤ 18) and K⁽ⁿ⁾(d) table | A.4, A.5 |
| `density_parallel.py` | Parallel density computation for large n (19–30) | A.4 (large n) |
| `conjecture_sequences.py` | Conjecture 6.1 verification across 11 generator sequences (prime + random) | A.6 |

## Requirements

```
Python >= 3.10
numpy
```

```bash
pip install numpy sympy
```

## Usage

```bash
# Verify the linear-time algorithm (Tables A.2, A.3)
python verify_linear_Q.py

# Verify incremental window builder + benchmark
python incremental_windows.py
python incremental_windows.py --verify   # verification only

# Reproduce density table A.4 (n=2..18) and K^(n)(d) table A.5
python appendix_verify.py
python appendix_verify.py --n-max 20 --table A4

# Parallel density computation for large n (Table A.4, n=19..30)
python density_parallel.py              # all cores
python density_parallel.py 19 30 8     # n=19..30, 8 cores
```

## Algorithm summary

**Theorem 1.1** (two generators).  
Q(**n**) = Σₖ nₖ (W⁺ₖ − W⁻ₖ) where W⁺, W⁻ are sliding-window sums.  
Cost: O(N) with four monotone pointers on the gap set G.

**Theorem 1.2** (n generators).  
The generalised kernel K⁽ⁿ⁾ defined by inclusion–exclusion over 2ⁿ subsets  
has at most w(n) ≤ σₙ active intervals due to parity cancellation.  
The active windows are computable incrementally in O(n · σₙ).

**Theorem 1.5** (density asymptotics).  
For generators satisfying log pₙ = o(n):  
w(n) / (2ⁿ − 1) = o(∏ᵢ (1 − 1/pᵢ)), equivalently δ(n)/P(n) → 1.

```bash
# Verify Conjecture 6.1 across multiple sequences (Table A.6)
python conjecture_sequences.py                      # n=25, summary
python conjecture_sequences.py --n-end 300          # full paper run (~60s)
python conjecture_sequences.py --n-end 25 --no-random
```
