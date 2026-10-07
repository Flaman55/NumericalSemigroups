"""
core.py
=======
Shared building blocks for the linear-Q numerical semigroup algorithms.

Reference:
  Artur Flamandzki, "A Linear Algorithm for Huang's Quadratic Form
  on Numerical Semigroups and Density Asymptotics", 2026.
"""

from itertools import combinations
from math import gcd, prod

# First 40 primes — used as canonical generator sequence in density experiments.
PRIMES = [
     2,  3,  5,  7, 11, 13, 17, 19, 23, 29,
    31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97,101,103,107,109,113,
   127,131,137,139,149,151,157,163,167,173,
]


# ------------------------------------------------------------------ #
#  Gap sets
# ------------------------------------------------------------------ #

def gap_set(a: int, b: int) -> list[int]:
    """
    Sorted list of gaps of the numerical semigroup <a, b>.

    By the Sylvester-Frobenius theorem the gap set is finite with
    |G| = (a-1)(b-1)/2.  Requires gcd(a, b) = 1.
    """
    assert gcd(a, b) == 1 and a > 1 and b > 1, "Need gcd(a,b)=1, a,b > 1"
    frob = a * b - a - b
    sg: set[int] = set()
    for i in range(a + 1):
        for j in range(b + 1):
            v = i * a + j * b
            if v <= frob + max(a, b):
                sg.add(v)
    return sorted(x for x in range(1, frob + 1) if x not in sg)


def gap_set_multi(gens: list[int]) -> list[int]:
    """
    Sorted list of gaps of the numerical semigroup <p_1, ..., p_n>.

    Uses BFS up to a safe upper bound.  For two generators prefer
    the faster `gap_set(a, b)`.
    """
    bound = max(gens) * sum(gens) * 2
    sg: set[int] = {0}
    changed = True
    while changed:
        new = {s + g for s in sg for g in gens if s + g <= bound} - sg
        changed = bool(new)
        sg |= new
    cands = [x for x in range(bound + 1) if x not in sg]
    frob = max(cands) if cands else 0
    return sorted(x for x in range(1, frob + 1) if x not in sg)


# ------------------------------------------------------------------ #
#  Kernels  K  and  K^(n)
# ------------------------------------------------------------------ #

def K(d: int, a: int, b: int) -> int:
    """
    Two-generator kernel (Lemma 2.1):
      K(d) = 1_{d>=0} - 1_{d>=a} - 1_{d>=b} + 1_{d>=a+b}

    Nonzero exactly on [0, a) (value +1) and [b, a+b) (value -1).
    """
    return (
        (1 if d >= 0   else 0)
      - (1 if d >= a   else 0)
      - (1 if d >= b   else 0)
      + (1 if d >= a+b else 0)
    )


def K_multi(d: int, gens: list[int]) -> int:
    """
    Multi-generator kernel (Definition 1.3):
      K^(n)(d) = sum_{S subset gens} (-1)^|S| * 1_{d >= sigma(S)}

    O(2^n) evaluation — use IncrementalWindowBuilder for repeated queries.
    """
    total = 0
    for r in range(len(gens) + 1):
        for S in combinations(gens, r):
            if d >= sum(S):
                total += (-1) ** r
    return total


# ------------------------------------------------------------------ #
#  Active windows  (naive O(2^n) — for small n or verification)
# ------------------------------------------------------------------ #

def active_windows(gens: list[int]) -> list[tuple[int, int, int]]:
    """
    Return list of (lo, hi, K_value) for each interval [lo, hi) where
    K^(n) != 0.  Naive O(2^n) computation of all subset sums.

    For n > ~20 use IncrementalWindowBuilder (incremental_windows.py).
    """
    bps: set[int] = set()
    for r in range(len(gens) + 1):
        for S in combinations(gens, r):
            bps.add(sum(S))
    bps_sorted = sorted(bps)

    wins = []
    for i in range(len(bps_sorted) - 1):
        kv = K_multi(bps_sorted[i], gens)
        if kv != 0:
            wins.append((bps_sorted[i], bps_sorted[i + 1], kv))
    return wins


def window_count(gens: list[int]) -> int:
    """Number of active windows w(n) — convenience wrapper."""
    return len(active_windows(gens))
