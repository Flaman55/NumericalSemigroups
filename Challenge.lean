module

public import Mathlib

/-!
# Advertised statements

This file is the small, trusted surface a mathematical reader should audit. It imports only
Mathlib and states the main results of the accompanying paper *A Linear Algorithm for Huang's
Quadratic Form on Numerical Semigroups and Density Asymptotics* (Flamandzki, 2026) for the
generalised kernel `K⁽ⁿ⁾`.

## Setting

For generators `p₁, …, pₙ`, the kernel is the inclusion–exclusion sum over all sub-multisets
`S` of the generators,

  `K⁽ⁿ⁾(d) = ∑_S (-1)^{|S|} · 𝟙_{d ≥ σ(S)}`,  `σ(S) = ∑_{p ∈ S} p`,

(`Submission.kernel`). It is a step function. Its jump at `s` is `π(s) = K(s) − K(s−1)`
(`Submission.jump`). An *active window* is an interval between consecutive breakpoints on
which the kernel is nonzero; `Submission.activeWindowCount` is the number `w(n)` of such
windows, counted by their left endpoints. The quadratic form is
`Q(n) = ∑_{i,j ∈ G} K⁽ⁿ⁾(j − i) · nᵢ · nⱼ` (`Submission.quadForm`) for any finite set `G` of
integers and any real weights `n : ℤ → ℝ`.

## Results

1. `Submission.quadForm_two_eq_linearForm2` (two generators): `Q` equals the sliding-window
   form `∑_k n_k (W⁺_k − W⁻_k)`, which is what turns the `O(N²)` double sum into two
   window sums.
2. `Submission.quadForm_eq_breakpoint_sum` and `Submission.breakpoints_card_le`
   (`n` generators): `Q(n)` is a sum over the breakpoints `s` of `π(s) · T(s)`, where
   `T(s) = ∑_{i,j ∈ G, j − i ≥ s} nᵢ nⱼ`, and there are at most `σ + 1` breakpoints.
3. `Submission.activeWindowCount_le_sigma`: `w(n) ≤ σ_n`.
4. `Submission.windowCount_isLittleO_mertensProd` and
   `Submission.gap_div_mertensProd_tendsto_one` (density asymptotics): for strictly increasing
   generators `pₖ ≥ 2` with `log pₙ = o(n)`, the density `w(n)/(2ⁿ − 1)` is `o(P(n))`, where
   `P(n) = ∏ₖ (1 − 1/pₖ)`; equivalently `δ(n)/P(n) → 1` for `δ(n) = P(n) − w(n)/(2ⁿ − 1)`.

No definition is left unspecified: all objects are defined here, and the Solution file defines
the same objects and proves the statements.
-/

/-- The generalised kernel `K⁽ⁿ⁾(d) = ∑_S (-1)^{|S|} · 𝟙_{d ≥ σ(S)}`, summed over all
sub-multisets `S` of the generator list `ps` (so repeated generators are counted with
multiplicity, as index subsets). -/
@[expose] public def Submission.kernel (ps : List ℕ) (d : ℤ) : ℤ :=
  (((ps : Multiset ℕ).powerset).map
    (fun t : Multiset ℕ =>
      (-1 : ℤ) ^ Multiset.card t * (if ((t.sum : ℕ) : ℤ) ≤ d then 1 else 0))).sum

/-- The jump (parity function) of the kernel at `s`: `π(s) = K(s) − K(s−1)`. It is nonzero
exactly at the breakpoints of the step function `K`. -/
@[expose] public def Submission.jump (ps : List ℕ) (s : ℤ) : ℤ :=
  Submission.kernel ps s - Submission.kernel ps (s - 1)

/-- `w(ps)`: the number of active windows of the kernel. Windows are the intervals
`[s, s')` between consecutive breakpoints; the window starting at the breakpoint `s ∈ [0, σ)` is
active when the kernel is nonzero on it. Windows are counted by their left endpoints. -/
@[expose] public def Submission.activeWindowCount (ps : List ℕ) : ℕ :=
  ((Finset.Ico (0 : ℤ) (ps.sum : ℤ)).filter
    (fun s => Submission.jump ps s ≠ 0 ∧ Submission.kernel ps s ≠ 0)).card

/-- The quadratic form `Q(n) = ∑_{i,j ∈ G} K⁽ⁿ⁾(j − i) · nᵢ · nⱼ`. -/
@[expose] public noncomputable def Submission.quadForm
    (ps : List ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, (Submission.kernel ps (j - i) : ℝ) * n i * n j

/-- The tail pair-sum `T(s) = ∑_{i,j ∈ G, j − i ≥ s} nᵢ nⱼ`. -/
@[expose] public noncomputable def Submission.pairTail
    (G : Finset ℤ) (n : ℤ → ℝ) (s : ℤ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, if s ≤ j - i then n i * n j else 0

/-- The breakpoints of the kernel, as natural numbers in `[0, σ]`. -/
@[expose] public def Submission.breakpoints (ps : List ℕ) : Finset ℕ :=
  (Finset.range (ps.sum + 1)).filter (fun k => Submission.jump ps (k : ℤ) ≠ 0)

/-- The sliding-window form for two generators `a < b`:
`∑_{k ∈ G} n_k (W⁺_k − W⁻_k)`, where `W⁺_k = ∑_{j ∈ G, k ≤ j < k + a} n_j` and
`W⁻_k = ∑_{j ∈ G, k + b ≤ j < k + a + b} n_j`. -/
@[expose] public noncomputable def Submission.linearForm2
    (a b : ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ k ∈ G, n k *
    ((∑ j ∈ G, if k ≤ j ∧ j < k + (a : ℤ) then n j else 0) -
      (∑ j ∈ G, if k + (b : ℤ) ≤ j ∧ j < k + (a : ℤ) + b then n j else 0))

/-- The density product `P(n) = ∏_{k<n} (1 − 1/pₖ)`. -/
@[expose] public noncomputable def Submission.mertensProd (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - 1 / (p k : ℝ))

/-- **Theorem 1.1 (two generators).** For `a < b`, the quadratic form equals the sliding-window
form: `Q(n) = ∑_k n_k (W⁺_k − W⁻_k)`. -/
public theorem Submission.quadForm_two_eq_linearForm2 (a b : ℕ) (hab : a < b)
    (G : Finset ℤ) (n : ℤ → ℝ) :
    Submission.quadForm [a, b] G n = Submission.linearForm2 a b G n := by
  sorry

/-- **Theorem 1.2, decomposition (`n` generators).** For a nonempty generator list, the
quadratic form is a sum over the breakpoints `s` of the kernel of `π(s) · T(s)`. -/
public theorem Submission.quadForm_eq_breakpoint_sum (ps : List ℕ) (hne : ps ≠ [])
    (G : Finset ℤ) (n : ℤ → ℝ) :
    Submission.quadForm ps G n =
      ∑ k ∈ Submission.breakpoints ps,
        (Submission.jump ps (k : ℤ) : ℝ) * Submission.pairTail G n (k : ℤ) := by
  sorry

/-- **Theorem 1.2, breakpoint count.** The kernel has at most `σ + 1` breakpoints. -/
public theorem Submission.breakpoints_card_le (ps : List ℕ) :
    (Submission.breakpoints ps).card ≤ ps.sum + 1 := by
  sorry

/-- **Theorem 1.2, window bound.** The number of active windows is at most `σ = ∑ pᵢ`. -/
public theorem Submission.activeWindowCount_le_sigma (ps : List ℕ) :
    Submission.activeWindowCount ps ≤ ps.sum := by
  sorry

/-- **Theorem 1.5 (density asymptotics).** For strictly increasing generators `pₖ ≥ 2` with
`log pₙ / n → 0`, the density of active windows `w(n)/(2ⁿ − 1)` is `o(P(n))`, where `w(n)` is
the number of active windows of the first `n` generators. -/
public theorem Submission.windowCount_isLittleO_mertensProd
    (p : ℕ → ℕ) (hge : ∀ k, 2 ≤ p k) (hord : StrictMono p)
    (hsub : Filter.Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) Filter.atTop (nhds 0)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ =>
        (Submission.activeWindowCount ((List.range n).map p) : ℝ) / ((2 : ℝ) ^ n - 1))
      (Submission.mertensProd p) := by
  sorry

/-- **Theorem 1.5, density defect form.** Under the same hypotheses,
`δ(n)/P(n) → 1`, where `δ(n) = P(n) − w(n)/(2ⁿ − 1)`. -/
public theorem Submission.gap_div_mertensProd_tendsto_one
    (p : ℕ → ℕ) (hge : ∀ k, 2 ≤ p k) (hord : StrictMono p)
    (hsub : Filter.Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Submission.mertensProd p n -
          (Submission.activeWindowCount ((List.range n).map p) : ℝ) / (2 ^ n - 1)) /
          Submission.mertensProd p n)
      Filter.atTop (nhds 1) := by
  sorry
