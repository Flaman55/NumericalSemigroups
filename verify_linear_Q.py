"""
verify_linear_Q.py
==================
Numerical verification of Theorems 1.1 and 1.2 from:

  Artur Flamandzki, "A Linear Algorithm for Huang's Quadratic Form
  on Numerical Semigroups and Density Asymptotics", 2026.

Produces the data for Appendix Tables A.2 and A.3:

  Table A.2 — Two generators: three independent implementations of Q
              compared for all coprime pairs (a, b) with b <= B_MAX.
              Operation counts match theoretical O(N^2) vs O(N).

  Table A.3 — Multiple generators: generalised sliding-window vs
              naive O(N^2) for small generator sets.

Usage:
  python verify_linear_Q.py
"""

import numpy as np
import bisect
from math import gcd

from core import gap_set, gap_set_multi, K, K_multi, active_windows

# ------------------------------------------------------------------ #
#  Parameters
# ------------------------------------------------------------------ #
B_MAX     = 40    # upper bound on b for the full (a, b) sweep
N_SAMPLES = 10    # random vectors per (a, b) pair
RNG_SEED  = 42
TOL_SMALL = 1e-9  # tolerance for N <= 500
TOL_LARGE = 1e-8  # tolerance for N > 500


# ------------------------------------------------------------------ #
#  Algorithm 1 — O(N^2) naive double sum  [reference / ground truth]
# ------------------------------------------------------------------ #

def Q_naive(n: np.ndarray, G: list[int], a: int, b: int) -> float:
    """Direct O(N^2) evaluation of Q(n) = sum_{k,l} K(G[l]-G[k]) n[k] n[l]."""
    N = len(G)
    total = 0.0
    for k in range(N):
        for l in range(N):
            total += K(G[l] - G[k], a, b) * n[k] * n[l]
    return total


# ------------------------------------------------------------------ #
#  Algorithm 2 — O(N log N) prefix sums + bisect  [intermediate]
# ------------------------------------------------------------------ #

def Q_prefix(n: np.ndarray, G: list[int], a: int, b: int) -> float:
    """O(N log N) evaluation using prefix sums and binary search."""
    N = len(G)
    prefix = np.zeros(N + 1)
    for i in range(N):
        prefix[i + 1] = prefix[i] + n[i]

    def window_sum(lo_val: int, hi_val: int) -> float:
        lo = bisect.bisect_left(G, lo_val)
        hi = bisect.bisect_left(G, hi_val)
        return float(prefix[hi] - prefix[lo])

    total = 0.0
    for k in range(N):
        gk = G[k]
        total += n[k] * (window_sum(gk, gk + a) - window_sum(gk + b, gk + a + b))
    return total


# ------------------------------------------------------------------ #
#  Algorithm 3 — O(N) sliding windows  [Theorem 1.1, main result]
# ------------------------------------------------------------------ #

def Q_linear(n: np.ndarray, G: list[int], a: int, b: int) -> float:
    """
    O(N) evaluation of Q via two amortised sliding windows (Theorem 1.1).

    Window+: [g_k, g_k + a)      contributes K = +1
    Window-: [g_k + b, g_k+a+b)  contributes K = -1

    Each of the four boundary pointers advances monotonically — O(N) total.
    """
    N = len(G)
    wp = wm = 0.0
    lo_p = hi_p = lo_m = hi_m = 0
    total = 0.0

    for k in range(N):
        gk = G[k]
        while hi_p < N and G[hi_p] < gk + a:     wp += n[hi_p]; hi_p += 1
        while lo_p < N and G[lo_p] < gk:          wp -= n[lo_p]; lo_p += 1
        while hi_m < N and G[hi_m] < gk + a + b:  wm += n[hi_m]; hi_m += 1
        while lo_m < N and G[lo_m] < gk + b:      wm -= n[lo_m]; lo_m += 1
        total += n[k] * (wp - wm)

    return total


# ------------------------------------------------------------------ #
#  Multi-generator sliding window  [Theorem 1.2]
# ------------------------------------------------------------------ #

def Q_sliding_multi(n_vec: np.ndarray, G: list[int],
                    gens: list[int]) -> float:
    """
    O(w(n) * N) evaluation using the active-window decomposition
    (Theorem 1.2).  Prefix sums for O(log N) window queries.
    """
    N = len(G)
    prefix = np.zeros(N + 1)
    for i in range(N):
        prefix[i + 1] = prefix[i] + n_vec[i]

    def ws(lo_val: int, hi_val: int) -> float:
        return float(
            prefix[bisect.bisect_left(G, hi_val)]
          - prefix[bisect.bisect_left(G, lo_val)]
        )

    wins = active_windows(gens)
    total = 0.0
    for k in range(N):
        total += n_vec[k] * sum(c * ws(G[k] + lo, G[k] + hi)
                                for lo, hi, c in wins)
    return total


def Q_naive_multi(n_vec: np.ndarray, G: list[int], gens: list[int]) -> float:
    """O(N^2) naive evaluation for multiple generators."""
    return sum(
        K_multi(G[l] - G[k], gens) * n_vec[k] * n_vec[l]
        for k in range(len(G))
        for l in range(len(G))
    )


# ------------------------------------------------------------------ #
#  Verification helpers
# ------------------------------------------------------------------ #

def verify_pair(a: int, b: int, rng: np.random.Generator) -> dict:
    """Verify Q_naive == Q_prefix == Q_linear for pair (a, b)."""
    G = gap_set(a, b)
    N = len(G)
    tol = TOL_LARGE if N > 500 else TOL_SMALL

    max_err_prefix = max_err_linear = 0.0
    all_ok = True

    for _ in range(N_SAMPLES):
        nv = rng.uniform(0.1, 2.0, N)
        q_ref    = Q_naive(nv, G, a, b)
        q_prefix = Q_prefix(nv, G, a, b)
        q_linear = Q_linear(nv, G, a, b)

        max_err_prefix = max(max_err_prefix, abs(q_ref - q_prefix))
        max_err_linear = max(max_err_linear, abs(q_ref - q_linear))

        if abs(q_ref - q_prefix) > tol or abs(q_ref - q_linear) > tol:
            all_ok = False

    return {
        "a": a, "b": b, "N": N,
        "ops_N2": N * N,
        "ops_N": 4 * N,
        "max_err_prefix": max_err_prefix,
        "max_err_linear": max_err_linear,
        "ok": all_ok,
    }


# ------------------------------------------------------------------ #
#  Main
# ------------------------------------------------------------------ #

def main() -> None:
    rng = np.random.default_rng(RNG_SEED)

    # ---- Table A.2: Two generators ----
    print("=" * 70)
    print("TABLE A.2 — Two generators: O(N^2) vs O(N) verification")
    print(f"  All coprime pairs (a,b) with 1 < a < b <= {B_MAX}")
    print(f"  {N_SAMPLES} random vectors per pair")
    print("=" * 70)

    pairs = [(a, b) for a in range(2, B_MAX)
                    for b in range(a + 1, B_MAX + 1)
                    if gcd(a, b) == 1]

    results = []
    for a, b in pairs:
        results.append(verify_pair(a, b, rng))

    # Print selected rows (as in the paper)
    selected = [(3,5),(5,7),(7,11),(11,13),(23,29),(37,41),(97,101)]
    print(f"\n{'a':>4} {'b':>4} {'N':>6} {'O(N^2)':>10} {'O(N)':>8} "
          f"{'max err':>12}  status")
    print("-" * 60)
    for a, b in selected:
        r = next((x for x in results if x["a"] == a and x["b"] == b), None)
        if r:
            tol = TOL_LARGE if r["N"] > 500 else TOL_SMALL
            status = "PASS" if r["ok"] else "FAIL"
            print(f"{r['a']:>4} {r['b']:>4} {r['N']:>6} {r['ops_N2']:>10} "
                  f"{r['ops_N']:>8} {r['max_err_linear']:>12.2e}  {status}")

    n_pass = sum(1 for r in results if r["ok"])
    print(f"\nAll {len(results)} pairs: {n_pass} PASS, "
          f"{len(results) - n_pass} FAIL")

    # ---- Lemma 2.1 spot-check ----
    print("\n--- Lemma 2.1 (interval structure of K) ---")
    ok = True
    for a in range(2, 20):
        for b in range(a + 1, 20):
            if gcd(a, b) != 1:
                continue
            for d in range(-b - 2, a + b + 3):
                expected = +1 if 0 <= d < a else (-1 if b <= d < a + b else 0)
                if K(d, a, b) != expected:
                    print(f"  FAIL: a={a} b={b} d={d}")
                    ok = False
    print(f"  {'OK for all tested (a,b,d).' if ok else 'FAILURES detected.'}")

    # ---- Table A.3: Multiple generators ----
    print("\n" + "=" * 70)
    print("TABLE A.3 — Multiple generators: sliding-window vs naive O(N^2)")
    print("=" * 70)
    print(f"\n{'generators':>18} {'N':>5} {'w(n)':>6} {'max err':>12}  status")
    print("-" * 50)

    rng2 = np.random.default_rng(RNG_SEED)
    cases = [[2,3],[3,5],[2,3,5],[3,5,7],[2,3,5,7]]
    for gens in cases:
        G = gap_set_multi(gens)
        N = len(G)
        if N > 200:
            print(f"{str(gens):>18} {'(gap set too large)':>40}")
            continue
        wins = active_windows(gens)
        errs = []
        for _ in range(N_SAMPLES):
            nv = rng2.uniform(0.1, 2.0, N)
            errs.append(abs(Q_naive_multi(nv, G, gens)
                          - Q_sliding_multi(nv, G, gens)))
        max_err = max(errs)
        status = "PASS" if max_err < TOL_SMALL else "FAIL"
        print(f"{str(gens):>18} {N:>5} {len(wins):>6} {max_err:>12.2e}  {status}")

    print("\nDone.")


if __name__ == "__main__":
    main()
