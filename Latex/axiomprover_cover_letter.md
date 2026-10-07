**Subject:** Independent extension of Huang's quadratic form — formalization proposal + a proof shortcut observation

Dear AxiomProver team,

I came across your post about autoformazing Yifeng Huang's paper on the quadratic form Q and the dinv statistic — and I have to say, it caught my attention immediately.

I am a professional software engineer with a long-standing interest in combinatorics and formal mathematics. Inspired by Huang's result and your formalization of it, I spent the past months writing an independent paper that extends his work in two directions: first, a linear-time algorithm for evaluating Q by reducing it to sliding-window sums; second, a generalization of the kernel K to numerical semigroups with n generators, together with an asymptotic result showing that the density of active windows satisfies w(n)/(2^n-1) = o(P(n)) as n → ∞.

The paper is available on Zenodo: https://doi.org/10.5281/zenodo.20261426

I would very much welcome AxiomProver's formalization of it in Lean 4 / Mathlib.

I also want to share an observation that emerged while writing — one I deliberately kept out of the paper itself, as it concerns your formalization of Huang rather than my own results.

While studying solution.lean, I noticed that the algebraic setup leading to the key expression

  2B(1_D, 1_E) = Σ_{(k,j)∈D×E} K(g_j − g_k) + Σ_{(k,j)∈E×D} K(g_j − g_k)

takes several hundred lines in solution.lean (through bilinFormUnsym_eq_arrow_diff,
north_shift_sum_eq_box, and related lemmas). My Theorem 1.1 — the linear reduction
Q(n) = Σ_k n_k(W⁺_k − W⁻_k) — together with bilinearity of B yields this expression
in a handful of lines. The combinatorial core (the blue/red cell bijections φ/ψ) remains
unchanged and equally hard; only the algebraic preamble is shortened.

This is not a criticism — Huang's proof is a remarkable piece of work and your formalization
of it is impressive. It is simply an observation that fell out naturally from a different angle
of approach, and I thought it might be of independent interest to a team thinking about proof
length and structure in formal combinatorics.

I would be happy to discuss either the paper or this observation further.

Best regards,
Artur Flamandzki
flamandzki.artur@gmail.com
