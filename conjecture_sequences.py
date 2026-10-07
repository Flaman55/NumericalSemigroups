"""
conjecture_sequences.py
=======================
Verifies Conjecture 6.1 (harmonic conjecture) across multiple generator
sequences, reproducing Appendix Table A.6 from:

  Artur Flamandzki, "A Linear Algorithm for Huang's Quadratic Form
  on Numerical Semigroups and Density Asymptotics", 2026.

For each generator sequence the script computes:
  w(n)   -- number of active windows (via IncrementalWindowBuilder)
  P(n)   -- density product  prod(1 - 1/p_i)
  delta  -- P(n) - w(n)/(2^n - 1)
  n*     -- first n with delta(n) > 0  (sign-change index)
  Gap/M  -- delta(n)/P(n)  (converges to 1 by Theorem 1.5)

Sequences tested:
  Prime sequences  -- first n primes, primes from 101/1009, every
                      other/third prime, twin primes, p≡3(mod 4),
                      p≡1(mod 4).
  Random sequences -- random odd integers with the same or different
                      harmonic sum H_n = sum(1/p_i) as the baseline.

Full results are written to an output file; terminal shows a summary.

Requirements: numpy, sympy

Usage:
  python conjecture_sequences.py                # n=25, summary only
  python conjecture_sequences.py --n-end 300    # n=300, all sequences
  python conjecture_sequences.py --n-end 25 --output results.txt
"""

import sys
import time
import argparse
from math import prod, gcd
from functools import reduce

import numpy as np
from sympy import isprime, nextprime

from incremental_windows import IncrementalWindowBuilder


# ------------------------------------------------------------------ #
#  Generator sequence constructors
# ------------------------------------------------------------------ #

def first_n_primes(n: int) -> list[int]:
    """First n primes: 2, 3, 5, 7, ..."""
    primes, p = [], 2
    while len(primes) < n:
        primes.append(p)
        p = nextprime(p)
    return primes


def primes_from(start: int, n: int) -> list[int]:
    """n primes starting at or above `start`."""
    primes = []
    p = start if isprime(start) else nextprime(start - 1)
    while len(primes) < n:
        primes.append(p)
        p = nextprime(p)
    return primes


def every_kth_prime(k: int, n: int) -> list[int]:
    """Every k-th prime: p_k, p_{2k}, p_{3k}, ..."""
    all_p = first_n_primes(k * n + 10)
    return [all_p[k * i - 1] for i in range(1, n + 1)]


def twin_primes_lower(n: int) -> list[int]:
    """Lower element of each twin prime pair: 3, 5, 11, 17, ..."""
    twins, p = [], 3
    while len(twins) < n:
        if isprime(p) and isprime(p + 2):
            twins.append(p)
        p += 2
    return twins


def primes_mod(a: int, d: int, n: int) -> list[int]:
    """n primes congruent to a (mod d)."""
    primes, k = [], 0
    while len(primes) < n:
        val = a + k * d
        if isprime(val):
            primes.append(val)
        k += 1
    return primes


def random_odd_sequence(n: int, seed: int,
                        target_harmonic: float | None = None) -> list[int]:
    """
    n random odd integers >= 3, pairwise distinct.

    If target_harmonic is given, the sequence is scaled so that
    sum(1/p_i, i=1..n) matches target_harmonic (same H_n as baseline).
    Otherwise the harmonic sum is unconstrained (different H_n).
    """
    rng = np.random.default_rng(seed)
    if target_harmonic is None:
        # Unconstrained: random odd numbers in [3, 500]
        pool = [x for x in range(3, 501) if x % 2 == 1]
        chosen = rng.choice(pool, size=n, replace=False).tolist()
        return sorted(int(x) for x in chosen)

    # Match harmonic sum: use primes scaled to hit target_harmonic roughly.
    # Simple approach: take baseline primes, shuffle order (H_n is same).
    baseline = first_n_primes(n)
    indices  = rng.permutation(len(baseline)).tolist()
    return [baseline[i] for i in indices]


# ------------------------------------------------------------------ #
#  Single-sequence computation
# ------------------------------------------------------------------ #

def compute_sequence(generators: list[int],
                     n_end: int) -> list[dict]:
    """
    Compute density rows for a generator sequence up to n_end.
    Returns list of dicts with keys: n, gen, w, P, delta, ratio.
    """
    builder = IncrementalWindowBuilder()
    rows = []
    for n in range(1, n_end + 1):
        builder.add_generator(generators[n - 1])
        w     = builder.window_count()
        P     = prod(1 - 1 / p for p in generators[:n])
        delta = P - w / (2 ** n - 1)
        ratio = delta / P if P > 1e-15 else float("nan")
        rows.append({
            "n": n, "gen": generators[n - 1],
            "w": w, "P": P, "delta": delta, "ratio": ratio,
        })
    return rows


# ------------------------------------------------------------------ #
#  Formatting helpers
# ------------------------------------------------------------------ #

COL_HEADER = (f"{'n':>4} {'gen':>6} {'w(n)':>8} {'P(n)':>8} "
              f"{'delta':>9} {'delta/P':>8} {'dw':>7}")


def format_row(r: dict, prev_w: int | None) -> str:
    dw = r["w"] - prev_w if prev_w is not None else 0
    ratio_str = f"{r['ratio']:>8.4f}" if not __import__("math").isnan(r["ratio"]) else "     nan"
    return (f"{r['n']:>4} {r['gen']:>6} {r['w']:>8} {r['P']:>8.4f} "
            f"{r['delta']:>+9.4f} {ratio_str} {dw:>7}")


# ------------------------------------------------------------------ #
#  Process one sequence: write full to file, summary to terminal
# ------------------------------------------------------------------ #

SHOW_ROWS = 10   # first/last N rows shown in terminal


def process_sequence(generators: list[int], n_end: int,
                     label: str, fh) -> dict:
    """Run one sequence, write full table to fh, print summary."""
    sep   = "=" * 65
    sep2  = "-" * 55

    header = f"\n{sep}\nSequence: {label}\n{sep}"
    if fh:
        fh.write(header + "\n")
        fh.write(COL_HEADER + "\n")
        fh.write(sep2 + "\n")
    print(header)
    print(COL_HEADER)
    print(sep2)

    t0   = time.perf_counter()
    rows = compute_sequence(generators, n_end)

    prev_w = None
    for i, r in enumerate(rows):
        line = format_row(r, prev_w)
        if fh:
            fh.write(line + "\n")
        if i < SHOW_ROWS or i >= len(rows) - SHOW_ROWS:
            print(line)
        elif i == SHOW_ROWS:
            omitted = len(rows) - 2 * SHOW_ROWS
            msg = f"  ... ({omitted} rows omitted — see output file) ..."
            print(msg)
        prev_w = r["w"]

    elapsed    = time.perf_counter() - t0
    n_star     = next((r["n"] for r in rows if r["delta"] > 0), None)
    last       = rows[-1]
    ratio_last = last["ratio"]

    summary = {
        "label":      label,
        "n_star":     n_star,
        "ratio_last": ratio_last,
        "w_last":     last["w"],
        "elapsed":    elapsed,
    }

    summary_text = (
        f"\n  n* (first delta>0): {n_star}\n"
        f"  delta/P at n={n_end}: {ratio_last:.6f}\n"
        f"  w(n) at n={n_end}:   {last['w']}\n"
        f"  Time: {elapsed:.3f}s"
    )
    if fh:
        fh.write(summary_text + "\n")
    print(summary_text)

    return summary


# ------------------------------------------------------------------ #
#  Table A.6 summary (matches paper format)
# ------------------------------------------------------------------ #

def print_table_a6(summaries: list[dict], n_end: int) -> None:
    print("\n" + "=" * 72)
    print(f"TABLE A.6 — Verification of Conjecture 6.1 (n*  and  delta/P at n={n_end})")
    print("=" * 72)
    print(f"\n{'Sequence':45} {'n*':>4} {'delta/P':>8}")
    print("-" * 62)
    for s in summaries:
        ratio_str = f"{s['ratio_last']:.4f}" if s["ratio_last"] == s["ratio_last"] else "  —"
        n_star_str = str(s["n_star"]) if s["n_star"] else "—"
        print(f"  {s['label']:43} {n_star_str:>4} {ratio_str:>8}")


# ------------------------------------------------------------------ #
#  Main
# ------------------------------------------------------------------ #

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Verify Conjecture 6.1 across multiple generator sequences "
                    "(Appendix Table A.6)")
    parser.add_argument("--n-end", type=int, default=25,
                        help="Maximum n per sequence (default: 25; "
                             "use 300 to reproduce the full paper table)")
    parser.add_argument("--output", type=str, default="",
                        help="Write full results to this file "
                             "(default: conjecture_sequences_results.txt)")
    parser.add_argument("--no-random", action="store_true",
                        help="Skip random-sequence rows")
    args = parser.parse_args()

    n_end       = args.n_end
    output_file = args.output or f"conjecture_sequences_n{n_end}.txt"

    # Harmonic sum of baseline (first n_end primes) — used by random sequences
    baseline_primes  = first_n_primes(n_end)
    baseline_harmonic = sum(1 / p for p in baseline_primes)

    sequences = [
        # --- Prime sequences ---
        (baseline_primes,
         f"First {n_end} primes (baseline)"),
        (primes_from(101, n_end),
         "Primes from 101"),
        (primes_from(1009, n_end),
         "Primes from 1009"),
        (every_kth_prime(2, n_end),
         "Every other prime (p_2, p_4, ...)"),
        (every_kth_prime(3, n_end),
         "Every third prime (p_3, p_6, ...)"),
        (twin_primes_lower(n_end),
         "Smaller of twin prime pairs"),
        (primes_mod(3, 4, n_end),
         "Primes ≡ 3 (mod 4)"),
        (primes_mod(5, 4, n_end),
         "Primes ≡ 1 (mod 4)"),
    ]

    if not args.no_random:
        sequences += [
            # --- Random sequences ---
            (random_odd_sequence(n_end, seed=42,
                                 target_harmonic=baseline_harmonic),
             "Random — same H_n as baseline (seed 42)"),
            (random_odd_sequence(n_end, seed=137,
                                 target_harmonic=baseline_harmonic),
             "Random — same H_n as baseline (seed 137)"),
            (random_odd_sequence(n_end, seed=42,
                                 target_harmonic=None),
             "Random — different H_n (seed 42)"),
        ]

    print(f"conjecture_sequences.py  |  {len(sequences)} sequences, n=2..{n_end}")
    print(f"Full output -> {output_file}\n")

    summaries = []
    with open(output_file, "w", encoding="utf-8") as fh:
        fh.write(f"Conjecture 6.1 verification: n=2..{n_end}\n")
        fh.write(f"Generated by conjecture_sequences.py\n")
        fh.write("=" * 65 + "\n\n")

        for seq, label in sequences:
            try:
                s = process_sequence(seq, n_end, label, fh)
                summaries.append(s)
            except Exception as e:
                msg = f"\n  ERROR in '{label}': {e}"
                fh.write(msg + "\n")
                print(msg)

    print_table_a6(summaries, n_end)
    print(f"\nFull results saved to: {output_file}")


if __name__ == "__main__":
    main()
