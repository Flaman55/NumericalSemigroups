"""
density_parallel.py
===================
Parallel computation of density data (Table A.4, large n) from:

  Artur Flamandzki, "A Linear Algorithm for Huang's Quadratic Form
  on Numerical Semigroups and Density Asymptotics", 2026.

Uses IncrementalWindowBuilder to compute w(n) in O(n * sigma_n)
instead of the naive O(2^n).  Each value of n is independent,
so the outer loop is parallelised across cores.

Usage:
  python density_parallel.py                   # n = 19..30, all cores
  python density_parallel.py 19 30 8           # n = 19..30, 8 cores
  python density_parallel.py 2  30 1           # n = 2..30,  single core

Equivalent to section_C_parallel.py from the original working directory,
refactored to use IncrementalWindowBuilder instead of naive O(2^n).
"""

import sys
import multiprocessing as mp
from math import prod

from core import PRIMES
from incremental_windows import IncrementalWindowBuilder


# ------------------------------------------------------------------ #
#  Per-n computation  (must be importable — no module-level side effects)
# ------------------------------------------------------------------ #

def compute_row(n: int) -> tuple:
    """
    Return one row of Table A.4 for the first n primes.

    Uses IncrementalWindowBuilder: adds p_1, ..., p_n sequentially,
    cost O(n * sigma_{n-1}).
    """
    builder = IncrementalWindowBuilder()
    for i in range(n):
        builder.add_generator(PRIMES[i])

    gens    = PRIMES[:n]
    w       = builder.window_count()
    max_w   = 2 ** n - 1
    P       = prod(1 - 1 / p for p in gens)
    density = w / max_w
    delta   = P - density
    sparsity = (1 - w / max_w) * 100

    return (n, max_w, w, P, sparsity, delta)


# ------------------------------------------------------------------ #
#  Main
# ------------------------------------------------------------------ #

def main() -> None:
    n_start = int(sys.argv[1]) if len(sys.argv) > 1 else 19
    n_end   = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    n_cores = int(sys.argv[3]) if len(sys.argv) > 3 else mp.cpu_count()

    ns = list(range(n_start, n_end + 1))
    print(f"density_parallel.py — n={n_start}..{n_end}, {n_cores} core(s)")
    print(f"Generators: first n primes (p_1=2, p_2=3, ...)\n")
    print(f"{'n':>3} {'2^n-1':>12} {'w(n)':>7} {'P(n)':>8} "
          f"{'Sparsity%':>10} {'delta(n)':>10}")
    print("-" * 58)

    results = []
    with mp.Pool(processes=min(n_cores, len(ns))) as pool:
        for row in pool.imap_unordered(compute_row, ns):
            n, max_w, w, P, sparsity, delta = row
            sign = "+" if delta >= 0 else ""
            print(f"{n:>3} {max_w:>12} {w:>7} {P:>8.4f} "
                  f"{sparsity:>9.1f}% {sign}{delta:>9.4f}", flush=True)
            results.append(row)

    print("\n--- Sorted by n ---")
    print(f"{'n':>3} {'2^n-1':>12} {'w(n)':>7} {'P(n)':>8} "
          f"{'Sparsity%':>10} {'delta(n)':>10}")
    print("-" * 58)
    for n, max_w, w, P, sparsity, delta in sorted(results):
        sign = "+" if delta >= 0 else ""
        print(f"{n:>3} {max_w:>12} {w:>7} {P:>8.4f} "
              f"{sparsity:>9.1f}% {sign}{delta:>9.4f}")


if __name__ == "__main__":
    main()
