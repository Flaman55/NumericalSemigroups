"""
appendix_verify.py
==================
Reproduces Appendix Tables A.4 and A.5 from:

  Artur Flamandzki, "A Linear Algorithm for Huang's Quadratic Form
  on Numerical Semigroups and Density Asymptotics", 2026.

  Table A.4 — Density data: w(n), P(n), sparsity, delta(n)
              for n = 2..18 (direct enumeration via incremental builder).

  Table A.5 — Selected values of K^(n)(d) for n = 2..12,
              illustrating activation/deactivation of positions.

For n = 19..30 (Table A.4 large-n rows) see density_parallel.py.

Usage:
  python appendix_verify.py
  python appendix_verify.py --n-max 20
"""

import argparse
from math import prod, log

from core import PRIMES, K_multi
from incremental_windows import IncrementalWindowBuilder


# ------------------------------------------------------------------ #
#  Table A.4 — Density data
# ------------------------------------------------------------------ #

def density_row(builder: IncrementalWindowBuilder, n: int) -> dict:
    """Compute one row of Table A.4 for the current builder state."""
    gens     = builder.gens
    w        = builder.window_count()
    sigma_n  = 2 ** n - 1          # number of non-empty subsets
    P        = prod(1 - 1 / p for p in gens)
    sparsity = 1 - w / sigma_n
    delta    = P - w / sigma_n

    return {
        "n":        n,
        "sigma_n":  sigma_n,
        "w":        w,
        "P":        P,
        "sparsity": sparsity,
        "delta":    delta,
    }


def print_table_a4(n_max: int) -> None:
    print("=" * 72)
    print("TABLE A.4 — Density data (Theorem 1.5)")
    print(f"  Generators: first n primes.  Direct enumeration for n=2..{n_max}.")
    print("=" * 72)
    print(f"\n{'n':>3} {'2^n-1':>10} {'w(n)':>6} {'P(n)':>8} "
          f"{'Sparsity%':>10} {'delta(n)':>10}")
    print("-" * 54)

    builder = IncrementalWindowBuilder()
    for n in range(1, n_max + 1):
        builder.add_generator(PRIMES[n - 1])
        if n < 2:
            continue
        r = density_row(builder, n)
        sparsity_pct = r["sparsity"] * 100
        sign = "+" if r["delta"] >= 0 else ""
        bold = " *" if r["delta"] == max(density_row(
            IncrementalWindowBuilder(), k
        )["delta"] for k in range(2, n_max + 1)) else ""
        print(f"{r['n']:>3} {r['sigma_n']:>10} {r['w']:>6} {r['P']:>8.4f} "
              f"{sparsity_pct:>9.1f}% {sign}{r['delta']:>9.4f}")


# ------------------------------------------------------------------ #
#  Table A.5 — K^(n)(d) activation / deactivation
# ------------------------------------------------------------------ #

# Positions to display in Table A.5 (chosen to illustrate behaviour)
TABLE_A5_POSITIONS = [0, 3, 5, 7, 8, 9, 10, 16, 17, 25, 47]
TABLE_A5_N_RANGE   = range(2, 13)   # n = 2..12


def print_table_a5() -> None:
    print("\n" + "=" * 72)
    print("TABLE A.5 — Selected values of K^(n)(d), n = 2..12")
    print("  Generators: first n primes.")
    print("  Dot (·) denotes K^(n)(d) = 0.")
    print("=" * 72)

    ns = list(TABLE_A5_N_RANGE)
    header = f"{'d':>4} |" + "".join(f" n={n:>2}" for n in ns)
    print("\n" + header)
    print("-" * len(header))

    for d in TABLE_A5_POSITIONS:
        row = f"{d:>4} |"
        for n in ns:
            gens = PRIMES[:n]
            kv = K_multi(d, gens)
            cell = f"{kv:>5}" if kv != 0 else "    ·"
            row += cell
        print(row)

    # Annotations
    print()
    print("Notes:")
    print("  d=8:  active at n=3, deactivated (K=0) from n=4 onward.")
    print("  d=17: K^(6)(17) = 2  (first example of |K^(n)(d)| = 2).")
    print("  d=47: K^(12)(47) = -3  (illustrates |K^(n)(d)| = 3).")
    print("  These motivate open problems (i) and (ii) in the paper.")


# ------------------------------------------------------------------ #
#  Main
# ------------------------------------------------------------------ #

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Reproduce Appendix Tables A.4 and A.5")
    parser.add_argument("--n-max", type=int, default=18,
                        help="Maximum n for Table A.4 (default: 18). "
                             "For n>18 use density_parallel.py.")
    parser.add_argument("--table", choices=["A4", "A5", "all"], default="all",
                        help="Which table to print (default: all)")
    args = parser.parse_args()

    if args.table in ("A4", "all"):
        print_table_a4(args.n_max)

    if args.table in ("A5", "all"):
        print_table_a5()

    print("\nDone.")


if __name__ == "__main__":
    main()
