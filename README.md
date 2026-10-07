# linear_Q — Numerical Verification Scripts

Verification and computation scripts accompanying the paper:

> **A Linear Algorithm for Huang's Quadratic Form on Numerical Semigroups and Density Asymptotics**  
> Artur Flamandzki, 2026

---

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
