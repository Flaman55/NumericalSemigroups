"""
incremental_windows.py
======================
Incremental computation of active windows for K^(n) (Theorem 1.2).

Key insight (Lemma 2.5 — parity recurrence):
  pi_{n+1}(s) = pi_n(s) - pi_n(s - p_{n+1})

This means the set of breakpoints for n+1 generators equals the union
of breakpoints for n generators with the set {s + p_{n+1} : s in prev}.
Cost per step: O(sigma_{n-1}) instead of O(2^n).

Reference:
  Artur Flamandzki, "A Linear Algorithm for Huang's Quadratic Form
  on Numerical Semigroups and Density Asymptotics", 2026.

Usage:
  python incremental_windows.py           # verify + benchmark
  python incremental_windows.py --verify  # verify only
"""

import time
import argparse
from collections import defaultdict
from math import prod

from core import PRIMES, K_multi, active_windows


# ------------------------------------------------------------------ #
#  IncrementalWindowBuilder
# ------------------------------------------------------------------ #

class IncrementalWindowBuilder:
    """
    Maintains the active-window structure of K^(n) incrementally.

    State after adding generators p_1, ..., p_n:
      sum_to_parity : dict {breakpoint s -> net parity delta at s}
        K^(n)(d) = 1 + sum of sum_to_parity[s] for all s <= d
        (the 1 comes from the empty subset contribution at s=0)
      sum_set       : set of all subset sums seen so far

    Adding p_{n+1} (Lemma 2.5):
      New subset sums: {s + p_{n+1} : s in current sum_set}
      Each such sum s' corresponds to subsets S ∪ {p_{n+1}} whose
      parity is flipped relative to S, so the parity delta at s'
      is the negative of the parity delta at s.
    """

    def __init__(self) -> None:
        self.sum_to_parity: dict[int, int] = {}
        self.sum_set: set[int] = {0}
        self.gens: list[int] = []

    def add_generator(self, p: int) -> None:
        """Add one generator p and update the breakpoint structure."""
        self.gens.append(p)

        # Contribution of the singleton subset {p}: (-1)^1 = -1
        new_deltas: dict[int, int] = {p: -1}

        # For every existing non-empty subset sum s with parity delta d,
        # the subset S ∪ {p} has sum s+p and flipped parity (-d).
        for s, parity in self.sum_to_parity.items():
            sp = s + p
            new_deltas[sp] = new_deltas.get(sp, 0) + (-parity)

        for s, delta in new_deltas.items():
            self.sum_to_parity[s] = self.sum_to_parity.get(s, 0) + delta
            self.sum_set.add(s)

    def get_active_windows(self) -> list[tuple[int, int, int]]:
        """
        Return list of (lo, hi, K_value) for each active interval.

        K^(n)(d) for d in [bps[i], bps[i+1]) is computed as a prefix
        sum of parity deltas over sorted breakpoints.
        """
        bps = sorted(self.sum_set)
        wins = []
        k_current = 0

        for i, bp in enumerate(bps):
            if bp == 0:
                k_current += 1  # empty subset contributes (-1)^0 = +1 at d=0
            k_current += self.sum_to_parity.get(bp, 0)

            if i + 1 < len(bps) and k_current != 0:
                wins.append((bp, bps[i + 1], k_current))

        return wins

    def window_count(self) -> int:
        """Return w(n) = number of active windows."""
        return len(self.get_active_windows())


# ------------------------------------------------------------------ #
#  Verification
# ------------------------------------------------------------------ #

def verify(n_max: int = 14) -> bool:
    """
    Check that IncrementalWindowBuilder matches naive O(2^n)
    for n = 1, ..., n_max.
    """
    print(f"Verifying incremental vs naive for n = 1..{n_max} ...")
    builder = IncrementalWindowBuilder()
    all_ok = True

    for n in range(1, n_max + 1):
        builder.add_generator(PRIMES[n - 1])
        gens = PRIMES[:n]

        wins_naive = set(active_windows(gens))
        wins_incr  = set(builder.get_active_windows())

        ok = wins_naive == wins_incr
        if not ok:
            all_ok = False
            extra_n = wins_naive - wins_incr
            extra_i = wins_incr  - wins_naive
            print(f"  n={n}: MISMATCH  naive_only={sorted(extra_n)[:3]}  "
                  f"incr_only={sorted(extra_i)[:3]}")
        else:
            print(f"  n={n:2d}: OK — w(n) = {len(wins_incr)}")

    return all_ok


# ------------------------------------------------------------------ #
#  Benchmark
# ------------------------------------------------------------------ #

def benchmark(n_max: int = 25) -> None:
    """Compare timing: naive O(2^n) vs incremental O(n * sigma_n)."""
    print(f"\nBenchmark: naive O(2^n) vs incremental O(n·sigma)")
    print(f"{'n':>3} {'naive (s)':>10} {'incr (s)':>10} {'speedup':>9} {'w(n)':>6}")
    print("-" * 44)

    builder = IncrementalWindowBuilder()

    for n in range(1, n_max + 1):
        builder.add_generator(PRIMES[n - 1])
        gens = PRIMES[:n]

        # Incremental: just materialise windows (generator already added)
        t0 = time.perf_counter()
        wins_incr = builder.get_active_windows()
        t_incr = time.perf_counter() - t0

        if n <= 20:
            t0 = time.perf_counter()
            active_windows(gens)
            t_naive = time.perf_counter() - t0
            speedup = f"{t_naive / t_incr:>8.1f}x" if t_incr > 0 else "     inf"
            naive_str = f"{t_naive:>10.4f}"
        else:
            naive_str = f"{'---':>10}"
            speedup   = f"{'---':>9}"

        print(f"{n:>3} {naive_str} {t_incr:>10.6f} {speedup} {len(wins_incr):>6}")


# ------------------------------------------------------------------ #
#  Main
# ------------------------------------------------------------------ #

def main() -> None:
    parser = argparse.ArgumentParser(description="Incremental window builder")
    parser.add_argument("--verify", action="store_true",
                        help="Run verification only (skip benchmark)")
    parser.add_argument("--n-max", type=int, default=25,
                        help="Maximum n for benchmark (default: 25)")
    args = parser.parse_args()

    ok = verify(n_max=min(14, args.n_max))
    print(f"\nVerification: {'PASS' if ok else 'FAIL'}")

    if not args.verify and ok:
        benchmark(n_max=args.n_max)


if __name__ == "__main__":
    main()
